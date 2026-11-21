"""Blast Radius selector (team Biomakers).

For each patch against sqlglot @ eb11aec, pick the tests that can catch it,
using a per-test line-coverage map and import maps built from the pinned
commit, then pack them onto workers to minimise busiest-worker time + 2 s/worker.
"""

import ast
import gzip
import json
import os
import re
import sys
from pathlib import Path

DATA = Path(os.environ.get("BR_DATA", "/data"))
APP = Path(__file__).resolve().parent
SRC = Path(os.environ.get("BR_SRC", "/src/sqlglot"))
MAP = APP / "map"
WORKER_MS = 2000
MAX_WORKERS = 8


def log(*a):
    print(*a, file=sys.stderr)


# ---------------------------------------------------------------- patches

HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def parse_patch(text):
    """-> {path: {"old": path|None, "new": path|None, "hunks": [...]}}"""
    files = {}
    cur = None
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("diff --git "):
            cur = {"old": None, "new": None, "hunks": [], "binary": False}
            m = re.match(r"diff --git a/(.*) b/(.*)$", line)
            if m:
                cur["old"], cur["new"] = m.group(1), m.group(2)
            files[cur["new"] or cur["old"]] = cur
        elif cur is not None and line.startswith("--- "):
            p = line[4:].strip()
            cur["old"] = None if p == "/dev/null" else re.sub(r"^a/", "", p)
        elif cur is not None and line.startswith("+++ "):
            p = line[4:].strip()
            cur["new"] = None if p == "/dev/null" else re.sub(r"^b/", "", p)
        elif cur is not None and line.startswith("Binary files"):
            cur["binary"] = True
        elif cur is not None and line.startswith("@@"):
            m = HUNK.match(line)
            o, ol = int(m.group(1)), int(m.group(2) or 1)
            n, nl = int(m.group(3)), int(m.group(4) or 1)
            body = []
            i += 1
            co, cn = ol, nl
            while i < len(lines) and (co > 0 or cn > 0):
                l = lines[i]
                if l.startswith("\\"):
                    i += 1
                    continue
                tag = l[:1] if l else " "
                body.append((tag, l[1:]))
                if tag in " -":
                    co -= 1
                if tag in " +":
                    cn -= 1
                i += 1
            # swallow "\ No newline" marker
            while i < len(lines) and lines[i].startswith("\\"):
                i += 1
            cur["hunks"].append((o, n, body))
            continue
        i += 1
    return files


def apply_hunks(old_text, hunks):
    old = old_text.split("\n")
    out = []
    pos = 0  # index into old (0-based)
    for o, n, body in hunks:
        start = o - 1 if o > 0 else 0
        out.extend(old[pos:start])
        pos = start
        for tag, txt in body:
            if tag == " ":
                out.append(old[pos] if pos < len(old) else txt)
                pos += 1
            elif tag == "-":
                pos += 1
            elif tag == "+":
                out.append(txt)
    out.extend(old[pos:])
    return "\n".join(out)


def changed_old_lines(hunks):
    """Old-file line numbers touched: removed lines, plus both neighbours of
    pure insertions."""
    touched = set()
    for o, n, body in hunks:
        ln = o
        prev_ctx = None
        pending_insert = False
        for tag, txt in body:
            if tag == " ":
                if pending_insert:
                    touched.add(ln)
                    if prev_ctx:
                        touched.add(prev_ctx)
                    pending_insert = False
                prev_ctx = ln
                ln += 1
            elif tag == "-":
                touched.add(ln)
                prev_ctx = ln
                ln += 1
            elif tag == "+":
                pending_insert = True
        if pending_insert:
            touched.add(ln)
            if prev_ctx:
                touched.add(prev_ctx)
    return touched


# ---------------------------------------------------------------- maps


class Maps:
    def __init__(self, tests):
        self.tests = tests
        self.ids = json.loads((MAP / "ids.json").read_text())
        self.by_id = {t["id"]: t["number"] for t in tests}
        self.dur = {t["number"]: round(t["seconds"] * 1000) for t in tests}
        self.all = [t["number"] for t in tests]
        # map index -> runtime number (ids we map but are not in tests.json drop)
        self.num = [self.by_id.get(i) for i in self.ids]
        self._cov = {}
        self.extra = json.loads((MAP / "extra.json").read_text()) if (MAP / "extra.json").exists() else {}
        self.by_file = {}
        for t in tests:
            self.by_file.setdefault(t["file"], []).append(t["number"])

    def cov(self, path):
        if path not in self._cov:
            fn = MAP / "cov" / (path.replace("/", "__") + ".json.gz")
            if fn.exists():
                with gzip.open(fn, "rt") as f:
                    self._cov[path] = json.load(f)
            else:
                self._cov[path] = None
        return self._cov[path]

    def tests_of(self, idxs):
        out = set()
        for i in idxs:
            n = self.num[i] if 0 <= i < len(self.num) else None
            if n is not None:
                out.add(n)
        return out


# ---------------------------------------------------------------- python analysis


def strip_ast(text):
    try:
        tree = ast.parse(text)
    except SyntaxError:
        return None
    return tree


def norm(node):
    return ast.dump(node, annotate_fields=True, include_attributes=False)


def scopes(tree):
    """List of (node, kind, start, end, qualname) for every def/class."""
    out = []

    def walk(node, prefix):
        for ch in ast.iter_child_nodes(node):
            if isinstance(ch, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                start = min([ch.lineno] + [d.lineno for d in ch.decorator_list])
                q = prefix + ch.name
                out.append((ch, "class" if isinstance(ch, ast.ClassDef) else "def", start, ch.end_lineno, q))
                walk(ch, q + ".")
            else:
                walk(ch, prefix)

    walk(tree, "")
    return out


def assigned_names(stmt):
    names = set()
    for node in ast.walk(stmt):
        if isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
            names.add(node.id)
        elif isinstance(node, ast.Attribute) and isinstance(node.ctx, ast.Store):
            names.add(node.attr)
        elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.add(node.name)
        elif isinstance(node, ast.alias):
            names.add((node.asname or node.name).split(".")[0])
    return names


def stmt_at(tree, line):
    """Innermost statement containing line."""
    best = None
    for node in ast.walk(tree):
        if isinstance(node, ast.stmt) and node.lineno <= line <= (node.end_lineno or node.lineno):
            if best is None or (node.end_lineno - node.lineno) <= (best.end_lineno - best.lineno):
                best = node
    return best


def top_stmt_at(body, line):
    for node in body:
        if node.lineno <= line <= node.end_lineno:
            return node
    return None


# ---------------------------------------------------------------- selection


class Selector:
    def __init__(self, maps):
        self.m = maps
        self._src = {}
        self._name_index = None

    def src(self, path):
        if path not in self._src:
            p = SRC / path
            self._src[path] = p.read_text(encoding="utf-8") if p.exists() else None
        return self._src[path]

    def module_users(self, path, family=True):
        """Tests that execute any line of this module beyond import time
        (for a dialect, of any of its dialect/parser/generator/typing modules)."""
        paths = [path]
        base = path.rsplit("/", 1)[-1]
        if family and any(path.startswith("sqlglot/" + d + "/") for d in ("dialects", "parsers", "generators", "typing")):
            for d in ("dialects", "parsers", "generators", "typing"):
                q = "sqlglot/%s/%s" % (d, base)
                if q not in paths:
                    paths.append(q)
        out = set()
        for q in paths:
            cov = self.m.cov(q)
            if cov:
                for l, v in cov.items():
                    out.update(v[1:])
        return self.m.tests_of(out)

    def name_readers(self, names, restrict_paths=None):
        """Tests covering any (non-import) line in sqlglot/ that mentions one of names."""
        if self._name_index is None:
            self._name_index = json.loads((MAP / "names.json").read_text()) if (MAP / "names.json").exists() else {}
        out = set()
        for nm in names:
            for path, lines in self._name_index.get(nm, {}).items():
                cov = self.m.cov(path)
                if not cov:
                    continue
                for l in lines:
                    v = cov.get(str(l))
                    if v:
                        out.update(v[1:])
        return self.m.tests_of(out)

    def select_py_src(self, path, fp):
        """A change to a sqlglot/ python file."""
        old = self.src(path)
        if old is None:
            return None  # new file: unknown
        new = apply_hunks(old, fp["hunks"])
        t_old, t_new = strip_ast(old), strip_ast(new)
        if t_new is None:
            # syntax error: every test that imports sqlglot fails at import
            return "ALL"
        if t_old is not None and norm(t_old) == norm(t_new):
            # comments / formatting only.  Docstrings are part of the AST, so
            # this really cannot change behaviour.
            return set()
        cov = self.m.cov(path) or {}
        sel = set()
        unresolved = False
        for line in sorted(changed_old_lines(fp["hunks"])):
            v = cov.get(str(line))
            st = stmt_at(t_old, line) if t_old is not None else None
            span = [line]
            if st is not None:
                end = st.end_lineno
                body = getattr(st, "body", None)
                if isinstance(body, list) and body and not isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    end = max(st.lineno, body[0].lineno - 1)
                if not isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                    span = range(st.lineno, end + 1)
            for l in span:
                vv = cov.get(str(l))
                if vv and len(vv) > 1:
                    sel |= self.m.tests_of(vv[1:])
                    if v is None:
                        v = vv
            if v and v[0] == 1 or st is None or (v is None and st is not None):
                # executed only at import time (or not covered at all):
                # work out what the statement defines and who uses it.
                sel |= self.import_level(path, t_old, line, cov)
        return sel

    def import_level(self, path, tree, line, cov):
        if tree is None:
            return self.module_users(path)
        # innermost def containing the line?
        best = None
        for node, kind, s, e, q in scopes(tree):
            if s <= line <= e and (best is None or (e - s) < (best[3] - best[2])):
                best = (node, kind, s, e, q)
        if best and best[1] == "def":
            node, kind, s, e, q = best
            body_start = node.body[0].lineno
            if line >= body_start:
                # inside a function body but never executed by any test:
                # nothing can observe it ... unless it's not covered at all
                # because it's e.g. a nested def; use the enclosing def's runners.
                v = cov.get(str(line))
                if v is None:
                    runners = set()
                    for l in range(s, e + 1):
                        vv = cov.get(str(l))
                        if vv and len(vv) > 1:
                            runners.update(vv[1:])
                    return self.m.tests_of(runners)
                return set()
            # signature / decorator / default arguments: whoever runs the body
            runners = set()
            for l in range(body_start, e + 1):
                vv = cov.get(str(l))
                if vv and len(vv) > 1:
                    runners.update(vv[1:])
            out = self.m.tests_of(runners)
            if node.decorator_list and line < node.lineno:
                out |= self.name_readers({node.name}) & self.module_users(path)
            return out
        # class body or module level statement
        st = None
        container = tree.body
        if best and best[1] == "class":
            container = best[0].body
        st = top_stmt_at(container, line)
        if st is None:
            st = stmt_at(tree, line)
        names = assigned_names(st) if st is not None else set()
        if isinstance(st, (ast.Import, ast.ImportFrom)):
            return self.module_users(path) | self.name_readers(names)
        users = self.module_users(path)
        if best and best[1] == "class" and best[0].name == "Tokenizer" or "tokens.py" in path:
            # tokenizer tables are read through generic code; be broad
            return users
        if not names:
            return users
        readers = self.name_readers(names)
        # also values inside the statement (e.g. dict entries mapping exp.Foo -> fn):
        refs = set()
        for node in ast.walk(st):
            if isinstance(node, ast.Attribute):
                refs.add(node.attr)
        sel = (readers & users) if readers else users
        if isinstance(st, (ast.Assign, ast.AnnAssign, ast.AugAssign)) and isinstance(getattr(st, "value", None), (ast.Dict, ast.Call, ast.Set, ast.List, ast.Tuple)):
            # a table entry: everyone using this module and the table
            sel = (readers & users) if readers else users
        return sel

    def select_test_file(self, path, fp):
        old = self.src(path)
        tests_here = self.m.by_file.get(path, [])
        if old is None:
            return set(tests_here)
        new = apply_hunks(old, fp["hunks"])
        t_old, t_new = strip_ast(old), strip_ast(new)
        if t_new is None:
            return set(tests_here)
        if t_old is not None and norm(t_old) == norm(t_new):
            return set()
        sel = set()
        byname = {}
        for t in self.m.tests:
            if t["file"] == path:
                byname.setdefault(t["id"].split("::")[-1], []).append(t["number"])
        sc = scopes(t_old)
        for line in changed_old_lines(fp["hunks"]):
            hit = None
            for node, kind, s, e, q in sc:
                if kind == "def" and s <= line <= e and q.count(".") == 1:
                    hit = node.name
            if hit and hit.startswith("test") and hit in byname:
                sel |= set(byname[hit])
            else:
                # helper method / class or module level: whole file (and users)
                importers = self.m.extra.get("test_module_users", {}).get(path, {})
                if importers:
                    cls = None
                    for node, kind, s, e, q in sc:
                        if kind == "class" and s <= line <= e and "." not in q:
                            cls = node.name
                    for f, nm in importers.items():
                        if cls is None or cls in nm:
                            sel |= set(self.m.by_file.get(f, []))
                if hit:
                    users = set()
                    for node, kind, s, e, q in sc:
                        if kind == "def" and hit in ast.unparse(node) and node.name in byname:
                            users |= set(byname[node.name])
                    sel |= users if users else set(tests_here)
                else:
                    sel |= set(tests_here)
        return sel

    def select_fixture(self, path):
        refs = self.m.extra.get("fixtures", {})
        hit = refs.get(path)
        if hit is not None:
            return {self.m.by_id[i] for i in hit if i in self.m.by_id}
        return None

    def select(self, patch_text):
        files = parse_patch(patch_text)
        sel = set()
        for path, fp in files.items():
            p_old = fp["old"] or path
            if fp.get("binary"):
                r = self.select_fixture(p_old)
                sel |= r if r is not None else set(self.m.all)
                continue
            if p_old.startswith("sqlglot/") and p_old.endswith(".py"):
                r = self.select_py_src(p_old, fp)
            elif p_old.startswith("tests/") and p_old.endswith(".py") and "/fixtures/" not in p_old:
                base = p_old.rsplit("/", 1)[-1]
                if base.startswith("test_"):
                    r = self.select_test_file(p_old, fp)
                else:
                    r = self.select_helper(p_old, fp)
            elif p_old.startswith("tests/"):
                r = self.select_fixture(p_old)
                if r is None:
                    r = self.fixture_fallback(p_old)
            elif p_old.endswith((".md", ".txt", ".rst")) or p_old.startswith(("docs/", ".github/")):
                r = set()
            else:
                r = None
            if r == "ALL" or r is None:
                log("broad:", path)
                return set(self.m.all)
            sel |= r
        return sel

    def select_helper(self, path, fp):
        # tests/helpers.py etc: tests in files importing it, narrowed by symbol
        users = self.m.extra.get("helper_users", {}).get(path)
        if users is None:
            return None
        old = self.src(path)
        t_old = strip_ast(old) if old else None
        new = apply_hunks(old, fp["hunks"]) if old else None
        if t_old is not None and new is not None:
            t_new = strip_ast(new)
            if t_new is not None and norm(t_old) == norm(t_new):
                return set()
        names = set()
        if t_old is not None:
            for line in changed_old_lines(fp["hunks"]):
                st = top_stmt_at(t_old.body, line)
                if st is not None:
                    names |= assigned_names(st) if not isinstance(st, (ast.FunctionDef, ast.ClassDef)) else {st.name}
        out = set()
        for f, by in users.items():
            if names and not (names & set(by.get("names", []))) and not by.get("star"):
                continue
            out |= set(self.m.by_file.get(f, []))
        return out

    def fixture_fallback(self, path):
        base = path.rsplit("/", 1)[-1].split(".")[0]
        out = set()
        for f, nums in self.m.by_file.items():
            s = self.src(f)
            if s and base in s:
                out |= set(nums)
        return out if out else None


# ---------------------------------------------------------------- packing


def pack(nums, dur):
    nums = sorted(nums, key=lambda n: (-dur[n], n))
    if not nums:
        return []
    total = sum(dur[n] for n in nums)
    best = None
    for w in range(1, MAX_WORKERS + 1):
        if w > len(nums):
            break
        loads = [0] * w
        bins = [[] for _ in range(w)]
        for n in nums:
            k = loads.index(min(loads))
            bins[k].append(n)
            loads[k] += dur[n]
        cost = max(loads) + WORKER_MS * w
        if best is None or cost < best[0]:
            best = (cost, bins)
        if max(dur[nums[0]], total / (w + 1)) + WORKER_MS * (w + 1) >= best[0]:
            break
    return [b for b in best[1] if b]


def main():
    tests = json.loads((DATA / "tests.json").read_text())["tests"]
    maps = Maps(tests)
    sel = Selector(maps)
    out = []
    for p in sorted((DATA / "commits").glob("*.patch")):
        cid = p.stem
        try:
            chosen = sel.select(p.read_text(encoding="utf-8", errors="replace"))
        except Exception as e:  # never crash: fall back to everything
            log("error", cid, repr(e))
            chosen = set(maps.all)
        chosen = {n for n in chosen if n in maps.dur}
        out.append(json.dumps({"commit": cid, "workers": pack(chosen, maps.dur)}, separators=(",", ":")))
    sys.stdout.write("\n".join(out) + ("\n" if out else ""))


if __name__ == "__main__":
    main()
