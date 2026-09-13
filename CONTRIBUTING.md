# Working on the verification

Use the pinned Lean toolchain and Lake manifest. Run:

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/verify.py
```

Keep Q1-RD and Q1-SRD distinct, and state changes to hypotheses or definitions explicitly. Proofs must compile without admissions or additional mathematical axioms. Check any new public declarations in `Audit.lean`.

The source manifest deliberately binds this release's Lean files, audit declaration list and dependency pins. If you change them, review the changes first, then update their SHA-256 values and declaration inventory in `verification/source-manifest.json`. Add new Lean files to the manifest and remove deleted ones. A manifest update records new bytes; it does not establish that a theorem's mathematical meaning is unchanged. The verifier does not regenerate this record automatically.

Document mathematical references and preserve applicable upstream license notices for any copied or adapted code. The project license is Apache-2.0; third-party dependencies retain their own licenses. Include relevant build and axiom-check results with proposed changes.
