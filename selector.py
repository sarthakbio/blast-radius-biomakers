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


# ---------------------------------------------------------------- import check

_IMPORT_CHILD = r"""
import importlib.abc, importlib.util, json, sys
patched = json.loads(sys.stdin.read())
src_root = sys.argv[1]

class Finder(importlib.abc.MetaPathFinder):
    def find_spec(self, name, path, target=None):
        rel = name.replace(".", "/")
        for cand, is_pkg in ((rel + ".py", False), (rel + "/__init__.py", True)):
            if cand in patched:
                loader = Loader(cand)
                spec = importlib.util.spec_from_loader(name, loader, is_package=is_pkg, origin=src_root + "/" + cand)
                if is_pkg:
                    spec.submodule_search_locations = [src_root + "/" + rel]
                return spec
        return None

class Loader(importlib.abc.Loader):
    def __init__(self, rel):
        self.rel = rel
    def create_module(self, spec):
        return None
    def exec_module(self, module):
        module.__file__ = src_root + "/" + self.rel
        exec(compile(patched[self.rel], module.__file__, "exec"), module.__dict__)

sys.meta_path.insert(0, Finder())
sys.path.insert(0, src_root)
import logging
logging.disable(logging.CRITICAL)
import sqlglot
import sqlglot.expressions
import hashlib
from sqlglot.expressions import core as _core

def _fp_value(v, depth=0):
    if isinstance(v, _core.Expr):
        return repr(v)
    if depth < 2 and isinstance(v, (list, tuple, set, frozenset)):
        items = [_fp_value(x, depth + 1) for x in v]
        items = [x for x in items if x]
        return "[" + ",".join(sorted(items) if isinstance(v, (set, frozenset)) else items) + "]" if items else ""
    if depth < 2 and isinstance(v, dict):
        items = []
        for k, x in v.items():
            fx = _fp_value(x, depth + 1)
            if fx:
                items.append(repr(k) + ":" + fx)
        return "{" + ",".join(sorted(items)) + "}" if items else ""
    return ""

def fingerprint(mod):
    parts = []
    for name, v in sorted(vars(mod).items()):
        f = _fp_value(v)
        if f:
            parts.append(name + "=" + f)
        if isinstance(v, type) and getattr(v, "__module__", None) == mod.__name__:
            for an, av in sorted(vars(v).items()):
                f = _fp_value(av)
                if f:
                    parts.append(name + "." + an + "=" + f)
    return hashlib.sha1("\n".join(parts).encode()).hexdigest()

out = {}
for m in sys.argv[2:]:
    if m != "BASE":
        __import__(m)
        out[m] = fingerprint(sys.modules[m])
print(json.dumps(out))
"""


_BASE_READY = None


def _mod_name(rel):
    m = rel[:-3].replace("/", ".")
    return m[: -len(".__init__")] if m.endswith(".__init__") else m


def _fork_check(patched, modules):
    """Fast path: sqlglot is imported once (pristine) in this process; for
    patches that only touch modules not loaded yet (dialects, parsers,
    generators ...), fork and import them patched.  Returns stdout text, or
    None when the fast path does not apply."""
    global _BASE_READY
    if not hasattr(os, "fork"):
        return None
    if _BASE_READY is None:
        try:
            sys.path.insert(0, str(SRC))
            import logging

            logging.disable(logging.CRITICAL)
            import sqlglot  # noqa: F401
            import sqlglot.expressions  # noqa: F401

            _BASE_READY = True
        except Exception as e:
            log("base import failed", repr(e))
            _BASE_READY = False
    if not _BASE_READY or "BASE" in modules:
        return None
    if any(_mod_name(rel) in sys.modules for rel in patched):
        return None
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:  # child
        code = 1
        try:
            os.close(r)
            ns = {"__name__": "__brchild__"}
            body = _IMPORT_CHILD.split("import sqlglot\nimport sqlglot.expressions", 1)[1]
            head = _IMPORT_CHILD.split("sys.meta_path.insert(0, Finder())", 1)[0]
            import io as _io

            sys.stdin = _io.StringIO(json.dumps(patched))
            sys.argv = ["x", str(SRC)] + sorted(modules)
            buf = _io.StringIO()
            sys.stdout = buf
            exec(head + "sys.meta_path.insert(0, Finder())\n" + body, ns)
            os.write(w, buf.getvalue().encode())
            code = 0
        except BaseException:
            pass
        finally:
            os._exit(code)
    os.close(w)
    chunks = []
    while True:
        b = os.read(r, 65536)
        if not b:
            break
        chunks.append(b)
    os.close(r)
    _, status = os.waitpid(pid, 0)
    if os.WIFEXITED(status) and os.WEXITSTATUS(status) == 0:
        return b"".join(chunks).decode()
    return ""  # import failed


def import_check(patched, modules):
    """Import the given modules with the patched sources (in a child
    process, no network).  Returns True when every import succeeds."""
    import subprocess

    out = None
    try:
        out = _fork_check(patched, modules)
    except Exception as e:
        log("fork check error", repr(e))
        out = None
    if out is not None:
        if not out.strip():
            log("import check failed (fork)", sorted(modules))
            return False
        try:
            fps = json.loads(out.strip().splitlines()[-1])
        except Exception:
            return False
        ref = _fingerprints()
        changed = [m for m, h in fps.items() if m in ref and ref[m] != h]
        if changed:
            log("import-time objects changed", changed)
            return False
        return True

    try:
        r = subprocess.run(
            [sys.executable, "-S", "-c", _IMPORT_CHILD, str(SRC)] + sorted(modules),
            input=json.dumps(patched),
            capture_output=True,
            text=True,
            timeout=30,
            env={"PATH": os.environ.get("PATH", ""), "HOME": "/tmp", "PYTHONDONTWRITEBYTECODE": "1"},
        )
    except Exception as e:  # can't tell: assume it breaks
        log("import check error", repr(e))
        return False
    if r.returncode != 0:
        log("import check failed", modules, r.stderr.strip().splitlines()[-1:] if r.stderr else "")
        return False
    # module-level SQL objects built at import time must be unchanged too
    try:
        fps = json.loads(r.stdout.strip().splitlines()[-1])
    except Exception:
        return False
    ref = _fingerprints()
    changed = [m for m, h in fps.items() if m in ref and ref[m] != h]
    if changed:
        log("import-time objects changed", changed)
        return False
    return True


_FP = None


def _fingerprints():
    global _FP
    if _FP is None:
        fn = MAP / "fingerprints.json"
        _FP = json.loads(fn.read_text()) if fn.exists() else {}
    return _FP


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
        self.file_of = {t["number"]: t["file"] for t in tests}
        meta = ("::test_lazy_load", "test_dialect_imports.py::", "test_dialect_entry_points.py::")
        self.import_meta = {t["number"] for t in tests if any(m in t["id"] for m in meta)}

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


def same_code(a, b):
    """True when two sources tokenize identically once comments and blank
    lines are dropped, which implies the same AST."""
    import io
    import tokenize

    def toks(text):
        out = []
        for t in tokenize.generate_tokens(io.StringIO(text).readline):
            if t.type in (tokenize.COMMENT, tokenize.NL):
                continue
            out.append((t.type, t.string))
        return out

    try:
        return toks(a) == toks(b)
    except (tokenize.TokenError, IndentationError, SyntaxError):
        return False


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


_STMTS = {}


def stmt_at(tree, line):
    """Innermost statement containing line."""
    key = id(tree)
    if key not in _STMTS:
        _STMTS[key] = (tree, [n for n in ast.walk(tree) if isinstance(n, ast.stmt)])
    best = None
    for node in _STMTS[key][1]:
        if node.lineno <= line <= (node.end_lineno or node.lineno):
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
        self._subs = None
        self._tsrc = {}
        self._tsrc_pre = None
        self._trees = {}
        self._scopes = {}
        self._alltsrc = None
        self._cattrs = {}
        self.pad = [set(), set()]
        self.patched = {}
        self.imp_mods = set()
        self._impmap = None
        self._fxt = {}

    def scopes(self, path, tree):
        if path not in self._scopes:
            self._scopes[path] = scopes(tree)
        return self._scopes[path]

    def tree(self, path):
        if path not in self._trees:
            src = self.src(path)
            self._trees[path] = strip_ast(src) if src is not None else None
        return self._trees[path]

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
        if same_code(old, new):
            return set()
        t_old, t_new = self.tree(path), strip_ast(new)
        if t_new is None:
            # syntax error: every test that imports sqlglot fails at import
            return "ALL"
        cov = self.m.cov(path) or {}
        sel = set()
        self.patched[path] = new
        imp = self.impmap().get(path, {})
        for line in changed_old_lines(fp["hunks"]):
            for l in (line, line - 1, line + 1):
                for mname in imp.get(str(l), ()):
                    self.imp_mods.add(mname)
        if path.startswith("sqlglot/typing/"):
            # tests/test_typing.py imports every typing module and compares the
            # metadata tables (and annotator code) against their parents
            sel |= set(self.m.by_file.get("tests/test_typing.py", []))
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
            in_body = False
            if t_old is not None:
                for node, kind, s0, e0, q in self.scopes(path, t_old):
                    if kind == "def" and node.body[0].lineno <= line <= e0:
                        in_body = True
                        break
            # module / class level code runs at import time, which the coverage
            # map may have charged to whichever test imported the module first.
            if in_body and t_old is not None:
                # factory functions (they build closures/lambdas, often while the
                # module is imported): whoever runs the code they build.
                inner = None
                for node, kind, s0, e0, q in self.scopes(path, t_old):
                    if kind == "def" and s0 <= line <= e0 and (inner is None or e0 - s0 < inner[2] - inner[1]):
                        inner = (node, s0, e0)
                if inner is not None and any(isinstance(n, (ast.Lambda, ast.FunctionDef, ast.AsyncFunctionDef)) and n is not inner[0] for n in ast.walk(inner[0])):
                    for l in range(inner[1], inner[2] + 1):
                        vv = cov.get(str(l))
                        if vv and len(vv) > 1:
                            sel |= self.m.tests_of(vv[1:])
            # padding candidates (added only where they cost nothing)
            if t_old is not None:
                enclosing = None
                for node, kind, s0, e0, q in self.scopes(path, t_old):
                    if s0 <= line <= e0 and (enclosing is None or e0 - s0 < enclosing[1] - enclosing[0]):
                        enclosing = (s0, e0)
                lo, hi = enclosing if enclosing else (line - 10, line + 10)
                near = set()
                for l in range(lo, hi + 1):
                    vv = cov.get(str(l))
                    if vv and len(vv) > 1:
                        near.update(vv[1:])
                self.pad[0] |= self.m.tests_of(near)
            if not in_body:
                self.pad[0] |= self.m.import_meta
            if in_body and t_old is not None:
                sel |= self.persistent_effects(path, t_old, line, cov, v)
            if not in_body or v and v[0] == 1 or st is None or v is None:
                # executed only at import time (or not covered at all):
                # work out what the statement defines and who uses it.
                sel |= self.import_level(path, t_old, line, cov)
        return sel

    def def_runners(self, cov, s0, e0):
        out = set()
        for l in range(s0, e0 + 1):
            vv = cov.get(str(l))
            if vv and len(vv) > 1:
                out.update(vv[1:])
        return self.m.tests_of(out)

    def persistent_effects(self, path, tree, line, cov, v):
        """Code inside a function whose result outlives the call: run while the
        module is imported (metaclasses, __init_subclass__, table builders), or
        filling a cache on first use.  Coverage charges such lines only to the
        first test of each worker, so widen to everyone downstream."""
        inner = None
        for node, kind, s0, e0, q in self.scopes(path, tree):
            if kind == "def" and node.body[0].lineno <= line <= e0 and (inner is None or e0 - s0 < inner[2] - inner[1]):
                inner = (node, s0, e0, q)
        if inner is None:
            return set()
        node, s0, e0, q = inner
        out = set()
        ntests = (len(v) - 1) if v else 0
        if v and v[0] == 1 and ntests < 50:
            meta = node.name in ("__new__", "__init_subclass__", "__set_name__") or (
                node.name == "__init__" and "." in q and q.split(".")[-2].startswith("_"))
            if meta:
                log("broad: import-time class construction", path, line)
                return set(self.m.all)
            out |= self.name_readers({node.name}) | self.module_users(path) | self.def_runners(cov, s0, e0)
        # first-use caches: a branch that stores into a module/class level container
        globals_ = {t.id for n in tree.body if isinstance(n, (ast.Assign, ast.AnnAssign))
                    for t in (n.targets if isinstance(n, ast.Assign) else [n.target]) if isinstance(t, ast.Name)}
        for sub in ast.walk(node):
            if isinstance(sub, (ast.If, ast.For, ast.While, ast.Try, ast.With)) and sub.lineno <= line <= sub.end_lineno:
                for a in ast.walk(sub):
                    if isinstance(a, (ast.Assign, ast.AugAssign, ast.AnnAssign)):
                        tgts = a.targets if isinstance(a, ast.Assign) else [a.target]
                        for tg in tgts:
                            base = tg
                            while isinstance(base, (ast.Subscript, ast.Attribute)):
                                base = base.value
                            shared = False
                            # self.<attr>[...] = ... where <attr> is a class-level container
                            # (or named like a cache) is shared across instances and tests
                            if isinstance(tg, ast.Subscript) and isinstance(tg.value, ast.Attribute) and \
                                    isinstance(tg.value.value, ast.Name) and tg.value.value.id in ("self", "cls"):
                                attr = tg.value.attr
                                shared = "cache" in attr.lower() or attr in self.class_attrs(path, tree)
                            if shared or isinstance(base, ast.Name) and (base.id in globals_ or base.id == "cls" and tg is not base):
                                out |= self.def_runners(cov, s0, e0)
                                return out
        return out

    def class_attrs(self, path, tree):
        if path not in self._cattrs:
            names = set()
            for node in ast.walk(tree):
                if isinstance(node, ast.ClassDef):
                    for st in node.body:
                        if isinstance(st, (ast.Assign, ast.AnnAssign)) and isinstance(getattr(st, "value", None), (ast.Dict, ast.Call)):
                            names |= assigned_names(st)
            self._cattrs[path] = names
        return self._cattrs[path]

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
        sel = (readers & users) if readers else set(users)
        if best and best[1] == "class" and path.startswith("sqlglot/expressions/") and "." not in best[4]:
            # an Expression subclass's class-level data is only observable on
            # instances of it (or its subclasses): who names those classes in
            # code, plus tests whose SQL uses the function's SQL names.
            cls = best[0]
            cnames = {cls.name} | self.subclasses(cls.name)
            sel = self.name_readers(cnames | {c.lower() + "_sql" for c in cnames})
            words = set()
            for c in cnames:
                words.add(re.sub(r"(?<!^)(?=[A-Z])", "_", c).lower())
            for node in cls.body:
                if isinstance(node, (ast.Assign, ast.AnnAssign)) and "_sql_names" in assigned_names(node):
                    for c in ast.walk(node):
                        if isinstance(c, ast.Constant) and isinstance(c.value, str):
                            words.add(c.value.lower())
                    if node.lineno <= line <= node.end_lineno:
                        words |= self.line_literals(path, line)
            sel |= self.global_word_users(words)
            if len(cnames) > 1 or not sel:
                sel |= (readers & users) if readers else set(users)
            return sel | self.literal_users(path, st, line)
        if best and best[1] == "class":
            cls = best[0]
            # users of the class itself (and its subclasses): anything that
            # names it, plus its generator method by convention.
            cnames = {cls.name} | self.subclasses(cls.name)
            extra = self.name_readers(cnames | {c.lower() + "_sql" for c in cnames})
            if not any(path.startswith("sqlglot/" + d + "/") for d in ("dialects", "parsers", "generators", "typing")) or cls.name in ("Tokenizer",):
                sel |= extra
        # string keys / literals on the changed line: tests whose source names them
        sel |= self.literal_users(path, st, line)
        if not sel:
            sel = set(users)
        return sel

    def subclasses(self, name, depth=3):
        if self._subs is None:
            self._subs = json.loads((MAP / "subclasses.json").read_text()) if (MAP / "subclasses.json").exists() else {}
        out, frontier = set(), {name}
        for _ in range(depth):
            nxt = set()
            for n in frontier:
                nxt |= set(self._subs.get(n, ()))
            nxt -= out
            out |= nxt
            frontier = nxt
            if len(out) > 400:
                break
        return out

    def test_sources(self, files):
        if self._tsrc_pre is None:
            fn = MAP / "tsrc.json.gz"
            self._tsrc_pre = {}
            if fn.exists():
                with gzip.open(fn, "rt") as f:
                    pre = json.load(f)
                self._tsrc_pre = {self.m.by_id[k]: v for k, v in pre.items() if k in self.m.by_id}
        if self._tsrc_pre:
            wanted = set(files)
            return {n: src for n, src in self._tsrc_pre.items() if self.m.file_of[n] in wanted}
        out = {}
        for f in files:
            if f in self._tsrc:
                out.update(self._tsrc[f])
                continue
            d = {}
            src = self.src(f)
            if src:
                try:
                    tree = ast.parse(src)
                except SyntaxError:
                    tree = None
                if tree is not None:
                    lines = src.split("\n")
                    defs = {}
                    for node in ast.walk(tree):
                        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            defs.setdefault(node.name, []).append("\n".join(lines[node.lineno - 1:node.end_lineno]))
                    for t in self.m.tests:
                        if t["file"] == f:
                            nm = t["id"].split("::")[-1].split("[")[0]
                            d[t["number"]] = "\n".join(defs.get(nm, ())).lower()
            self._tsrc[f] = d
            out.update(d)
        return out

    def line_literals(self, path, line):
        old = self.src(path).split("\n")
        text = old[line - 1] if 0 < line <= len(old) else ""
        return set(m.lower() for m in re.findall(r"[\"']([A-Za-z_][A-Za-z0-9_]{2,})[\"']", text))

    def global_word_users(self, words):
        """Tests whose own source, or a fixture they read, contains one of the
        words (case-insensitive, whole word)."""
        words = {w for w in words if len(w) >= 3}
        if not words:
            return set()
        if self._alltsrc is None:
            self._alltsrc = self.test_sources(sorted(self.m.by_file))
        pat = re.compile(r"(?<![a-z0-9_])(" + "|".join(sorted(map(re.escape, words))) + r")(?![a-z0-9_])")
        out = {n for n, src in self._alltsrc.items() if pat.search(src)}
        fx = self.m.extra.get("fixtures", {})
        for path, ids in fx.items():
            txt = self.fixture_text(path)
            if txt and pat.search(txt):
                out |= {self.m.by_id[i] for i in ids if i in self.m.by_id}
        return out

    def fixture_text(self, path):
        if path not in self._fxt:
            t = None
            fn = MAP / "fixtures" / (path.replace("/", "__") + ".txt")
            if fn.exists():
                t = fn.read_text(encoding="utf-8", errors="replace").lower()
            self._fxt[path] = t
        return self._fxt[path]

    def literal_users(self, path, st, line):
        if st is None:
            return set()
        old = self.src(path).split("\n")
        text = old[line - 1] if 0 < line <= len(old) else ""
        lits = set(m.lower() for m in re.findall(r"[\"']([A-Za-z_][A-Za-z0-9_ ]{2,})[\"']", text))
        lits = {l for l in lits if len(l) >= 4 and l not in ("this", "expression", "expressions", "true", "false", "null")}
        if not lits:
            return set()
        base = path.rsplit("/", 1)[-1][:-3]
        bases = {base}
        tree = self.tree(path)
        if tree is not None:
            # dialects built on this one (e.g. Databricks on Spark) see the change too
            for node in tree.body:
                if isinstance(node, ast.ClassDef):
                    for sub in self.subclasses(node.name):
                        b = re.sub(r"(Parser|Generator|Tokenizer|Dialect|TypeAnnotator)$", "", sub).lower()
                        if b:
                            bases.add(b)
        files = [f for f in self.m.by_file if any(f.endswith("/test_" + b + ".py") for b in bases)]
        out = set()
        for n, src in self.test_sources(files).items():
            if any(l in src for l in lits):
                out.add(n)
        if any(path.startswith("sqlglot/" + d + "/") for d in ("dialects", "parsers", "generators", "typing")):
            # other dialects' tests that read or write this dialect and use the literal
            if self._alltsrc is None:
                self._alltsrc = self.test_sources(sorted(self.m.by_file))
            dpat = re.compile(r"[\"'](" + "|".join(sorted(map(re.escape, bases))) + r")[\"']")
            for n, src in self._alltsrc.items():
                if n not in out and any(l in src for l in lits) and dpat.search(src):
                    out.add(n)
        return out

    def select_test_file(self, path, fp):
        old = self.src(path)
        tests_here = self.m.by_file.get(path, [])
        if old is None:
            return set(tests_here)
        new = apply_hunks(old, fp["hunks"])
        if same_code(old, new):
            return set()
        t_old, t_new = self.tree(path), strip_ast(new)
        if t_new is None:
            return set(tests_here)
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

    def impmap(self):
        if self._impmap is None:
            fn = MAP / "impmap.json"
            self._impmap = json.loads(fn.read_text()) if fn.exists() else {}
        return self._impmap

    def import_breakers(self):
        """If the patched code fails while a module is being imported, every
        test that loads it can fail (in pytest-xdist, whichever test loads it
        first in each worker).  Check by importing; widen if it breaks."""
        if not self.imp_mods:
            return set()
        mods = set(self.imp_mods)
        if "BASE" in mods:
            # core tables feed the modules that parse/build SQL while importing
            mods |= set(self.m.extra.get("import_heavy", []))
        if import_check(self.patched, mods):
            return set()
        if "BASE" in mods and not import_check(self.patched, {"BASE"}):
            return "ALL"
        mods.discard("BASE")
        out = set()
        for m in mods:
            parts = m.split(".")
            base = parts[-1]
            path = "/".join(parts) + ".py"
            out |= self.module_users(path)
            if self.m.cov(path) is None:
                out |= self.module_users("/".join(parts) + "/__init__.py")
            # tests that name the dialect anywhere
            if len(parts) == 3 and parts[1] in ("dialects", "parsers", "generators", "typing"):
                if self._alltsrc is None:
                    self._alltsrc = self.test_sources(sorted(self.m.by_file))
                pat = re.compile(r"[\"']" + re.escape(base) + r"[\"']|\bin dialects\b|dialects\)|dialect\.classes|dialects\.")
                out |= {n for n, src in self._alltsrc.items() if pat.search(src)}
                for f, nums in self.m.by_file.items():
                    if f.endswith("/test_" + base + ".py"):
                        out |= set(nums)
            else:
                return "ALL"
        return out

    def select(self, patch_text):
        files = parse_patch(patch_text)
        sel = set()
        self.pad = [set(), set()]
        self.patched = {}
        self.imp_mods = set()
        for path, fp in files.items():
            p_old = fp["old"] or path
            if p_old.startswith("sqlglot/") and p_old.endswith(".py"):
                self.pad[1] |= self.module_users(p_old)
                base = p_old.rsplit("/", 1)[-1][:-3]
                for f, nums in self.m.by_file.items():
                    if f.endswith("/test_" + base + ".py"):
                        self.pad[1] |= set(nums)
            elif p_old.startswith("tests/"):
                if p_old.endswith(".py"):
                    self.pad[0] |= set(self.m.by_file.get(p_old, []))
                else:
                    fb = self.fixture_fallback(p_old)
                    if fb:
                        self.pad[1] |= fb
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
        if self.patched and self.imp_mods:
            # only test-import when every patched file is a sqlglot module
            r = self.import_breakers()
            if r == "ALL":
                log("broad: import breaks")
                return set(self.m.all)
            sel |= r
        return sel

    def select_helper(self, path, fp):
        # tests/helpers.py etc: tests in files importing it, narrowed by symbol
        if path.endswith("/__init__.py"):
            old = self.src(path) or ""
            if same_code(old, apply_hunks(old, fp["hunks"])):
                return set()
            d = path.rsplit("/", 1)[0] + "/"
            return {n for f, nums in self.m.by_file.items() if f.startswith(d) for n in nums}
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


def pad_workers(workers, cands, dur):
    """Add candidate tests to workers only where they do not raise the
    busiest worker's load (so the commit's cost is unchanged)."""
    if not workers:
        return workers
    loads = [sum(dur[n] for n in w) for w in workers]
    top = max(loads)
    have = {n for w in workers for n in w}
    for tier in cands:
        for n in sorted(tier - have, key=lambda n: (dur.get(n, 10 ** 9), n)):
            d = dur.get(n)
            if d is None:
                continue
            k = loads.index(min(loads))
            if loads[k] + d <= top:
                workers[k].append(n)
                loads[k] += d
                have.add(n)
    return workers


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
        # DIAGNOSTIC PROBE: everything for commits touching tests/
        if re.search(r"^diff --git a/tests/", p.read_text(encoding="utf-8", errors="replace"), re.M):
            chosen = set(maps.all)
        chosen = {n for n in chosen if n in maps.dur}
        workers = pack(chosen, maps.dur)
        try:
            workers = pad_workers(workers, getattr(sel, "pad", []), maps.dur)
        except Exception as e:
            log("pad error", cid, repr(e))
        out.append(json.dumps({"commit": cid, "workers": workers}, separators=(",", ":")))
    sys.stdout.write("\n".join(out) + ("\n" if out else ""))


if __name__ == "__main__":
    main()
