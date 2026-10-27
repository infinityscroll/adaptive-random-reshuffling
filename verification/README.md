# Verification evidence

`axiom-reports.txt` contains the declaration-and-axiom lines from the successful serial replay logs, in module replay order. Local-path warnings and operational records are excluded. It contains 397 printed reports, covering 395 distinct declarations; the final entrypoint repeats two earlier reports.

The recorded replay used Lean 4.27.0 and Mathlib commit `a3a10db0e9d66acbebf76c5e6a135066525ac900`.

| Check | Recorded result |
| --- | --- |
| Research modules rebuilt from source | 41 |
| Earlier research `.olean` files reused | None |
| Successful compiler calls | 41 |
| Axioms in printed reports | `propext`, `Classical.choice`, `Quot.sound` only |
| Aggregate child CPU | 292.316429 seconds |
| Overall elapsed wall time | 296.871339 seconds |
| External Lake workflow for this descriptor | Not executed |

Installed third-party compiler and library artifacts were reused. The replay is therefore a clean rebuild of the research modules, not of Lean, Mathlib, or all transitive dependencies. The corrected Lake descriptor registers all 41 source modules and was checked against the source set.

The paper's source and PDF hashes are:

```text
26858b4e35ace317466651ea118d06dbc9e45ad5d1d00bb4114c27f84659587b  paper/main.tex
1d69ad985538360ed7b0f705ae46ac59c7a717add9d32939457ccd6be8c2e80d  paper/adaptive-random-reshuffling.pdf
```

The PDF has 11 pages. Compilation, a complete mathematical/scope transcription review, and visual inspection of every page were recorded. These checks are not a claim of external peer review or novelty certification.

The formally proved conclusion is the actual expected-loss **lower bound**. The separately published upper theorem is cited in the paper; the formal two-sided sandwich remains conditional on that upper. No assumption of the desired lower risk is used in the final entrypoint.

Module identifiers retain their verified names. Relative paths and checksums in the repository are portable; private absolute paths, operational ledgers, correspondence, and compiled research binaries are not included.
