#!/usr/bin/env bash
set -euo pipefail
# Run from a fresh extraction of this package; requires Lean via elan and Python 3.
cd -- "$(dirname -- "$0")"
python3 - <<'PY'
import hashlib
from pathlib import Path
for row in Path("SHA256SUMS.txt").read_text().splitlines():
    digest, name = row.split("  ", 1)
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == digest, name
print("Release checksums verified")
PY
manifest_before=$(sha256sum lake-manifest.json)
lake exe cache get
lake build
lake env lean Audit.lean
test "$manifest_before" = "$(sha256sum lake-manifest.json)"
