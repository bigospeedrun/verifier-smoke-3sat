# OpenAI's 3-SAT proof, ported for the Big O Speedrun verifier

This branch (`port-openai`) is the port of OpenAI's Lean proof that the Big O Speedrun maintainers
submit to https://github.com/bigospeedrun/verifier for the `3sat` board
(https://bigospeedrun.com/3sat). Its purpose is the Lean Verified evidence level for OpenAI's
existing row (bound 1/2). The result is OpenAI's, and the row credits OpenAI alone. Big O Speedrun
shows only as "Ported by Big O Speedrun". This branch is not a new result.

The proof files are the same as on `main`, the maintainer smoke fixture that passed the verifier's
check chain (verifier issue #195). Only this README is different.

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

Other branches hold the maintainer smoke fixture (`main`), the control (the statement with `sorry`)
and statement mutations, each of which the verifier must refuse.

The repository holds no secrets and no workflows.
