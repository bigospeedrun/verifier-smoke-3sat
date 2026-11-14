# Verifier smoke fixture: 3-SAT

This repository exists only for the maintainer smoke test of the `3sat` profile of
https://github.com/bigospeedrun/verifier (board: https://bigospeedrun.com/3sat).
It is test data for the verifier. It is not a claim, not a submission and not a new result.
The board credits OpenAI's row as it is.

## Source

The proof is OpenAI's: https://github.com/openai/math at commit
`7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, theorem
`OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`
(Apache-2.0, see LICENSE, a copy of the upstream LICENSE).

- `OAI/`: the files of the upstream directory `lean/OAI/` that
  `OAI.Algorithms.SubexponentialSAT.Main` imports, directly or indirectly (3091 files). Each file is a
  byte copy of the upstream file. No file is changed, and no other upstream file is included.
- `Submission.lean` and `Submission/`: our files (Big O Speedrun maintainers), not OpenAI's.
  `Submission/ThreeSatStatement.lean` is the verifier's `challenges/3sat/Statement.lean`, with its first
  line replaced by imports of the OpenAI modules that define the same names.
  `Submission/Bridge.lean` derives the board target
  `BigOSpeedrun.ThreeSat.SolvedInTime (1 / 2)` from OpenAI's theorem with `k = 3`. It changes only the
  form of the statement (the trace projection, `0 < count ↔ satisfiable`, and the time bound
  comparison).

Branches other than `main` hold the control (the statement with `sorry`) and statement mutations,
each of which the verifier must refuse.

The repository holds no secrets and no workflows. It is archived (read-only) after the smoke passes.
