# Draft 5 verification environment
27 October 2026. Official Lean 4.19.0 Linux distribution, commit 6caaee842e94.

The six distributed source/configuration files (two libraries, Audit.lean,
lean-toolchain, lakefile.toml, lake-manifest.json) were archived and extracted
into a fresh directory with no .lake tree. Lake cloned all dependencies via
Git and fetched compiled mathlib dependencies with lake exe cache get.
lake build and lake env lean Audit.lean then completed successfully.
The manifest and all six input files were compared byte for byte with the
release files afterward. Every dependency HEAD matches its manifest revision.

The host cannot normally resolve /proc/self/exe. A small LD_PRELOAD readlink
fallback resolved the running executable from argv[0] and the official toolchain directory when that lookup failed.
LEAN_SYSROOT and LAKE_HOME identified the official installation; PATH selected
its binaries. TAR_OPTIONS=--no-same-owner avoids an extraction ownership issue.
No proof, kernel, library, manifest, or dependency source was modified by this
workaround. No local-path dependency manifest was used. These host settings
are not needed on a normal Lean installation and are not shipped as requirements.

CACHE_LOG.txt, BUILD_LOG.txt, AXIOM_AUDIT.txt and DEPENDENCY_REVISIONS.txt record
this run. The actual cache retrieval is part of the check; this is not a
from-source rebuild of all of mathlib. The clean build closes the previous
Git-manifest gap within this documented host environment.

The numerical scripts and reports are unchanged from v3, not new runs.
Only the draft labels in the Lean comments changed from v4; proof bodies
are unchanged. The PDF was recompiled and visually inspected for v5.
