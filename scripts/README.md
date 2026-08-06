# Software release packaging

`package_software.py` creates a deterministic, journal-neutral source archive
from a committed Git ref. It includes only the Lean artifact, its documentation,
license, citation metadata, and this packaging script.

Run all replay gates before packaging:

```bash
cd lean
lake exe cache get
lake build
lake build CollatzEndpointTransport.Linear.PaperAudit
lake build QuadraticAppendix
cd ..
```

Then package an immutable tag:

```bash
python3 scripts/package_software.py --version 2.0.1 --ref v2.0.1
```

The archive is written under `dist/v2.0.1/` unless `--output` is supplied.
The script prints the resolved commit, byte size, SHA-256, and MD5. It never
creates or moves a tag, pushes a branch, publishes a release, or changes
repository visibility.
