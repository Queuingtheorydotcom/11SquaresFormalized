FROM ubuntu:24.04
RUN apt-get update && apt-get install -y --no-install-recommends \
    python3 git curl tar xz-utils zstd ca-certificates \
    && rm -rf /var/lib/apt/lists/* \
    && groupadd -g 10001 proof && useradd -u 10001 -g 10001 -M proof \
    && mkdir -p /workspace && chown 10001:10001 /workspace
COPY runner.py /opt/eleven-square/runner.py
COPY fetch_wand125_release.py /opt/eleven-square/scripts/fetch_wand125_release.py
COPY metadata/ /opt/eleven-square/integrations/wand125/release/
COPY lake-manifest.json /opt/eleven-square/lake-manifest.json
ENV HOME=/workspace/home ELAN_HOME=/workspace/elan \
    XDG_CACHE_HOME=/workspace/cache TMPDIR=/workspace/tmp \
    PATH=/workspace/elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
USER 10001:10001
WORKDIR /workspace
ENTRYPOINT ["/usr/bin/python3", "-I", "/opt/eleven-square/runner.py"]
