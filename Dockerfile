# Team Biomakers - Blast Radius selector
FROM python:3.13-slim@sha256:e48f59cdba69a3cbd9ed2cf0f348d90d45a8d350d98134cf1070bc106ee9ed90
COPY selector.py /app/selector.py
COPY map.tgz /app/map.tgz
# map.tgz holds maps generated from sqlglot at the pinned commit eb11aec:
#   map/cov/*      per-test line coverage
#   map/names.json identifier -> source lines index
#   map/extra.json fixture readers, helper imports
#   map/src_py.tgz the pinned .py sources the patches apply to
RUN tar -xzf /app/map.tgz -C /app && rm /app/map.tgz \
 && mkdir -p /src/sqlglot && tar -xzf /app/map/src_py.tgz -C /src/sqlglot && rm /app/map/src_py.tgz \
 && chmod -R a+rX /app /src
ENV PYTHONDONTWRITEBYTECODE=1
CMD ["python", "-S", "/app/selector.py"]
