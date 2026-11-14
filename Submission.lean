import Submission.ThreeSatStatement
import Submission.Bridge

/-!
# Maintainer smoke fixture: `BigOSpeedrun.ThreeSat.SolvedInTime (1 / 2)`

Big O Speedrun verifier smoke (task 07840cc3). This file and the files under `Submission/` are
ours; they are not part of openai/math. Every file under `OAI/` is a byte copy of
https://github.com/openai/math at `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a` (directory
`lean/`), the import closure of `OAI.Algorithms.SubexponentialSAT.Main`. The proof is OpenAI's
(`OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`). `Submission/Bridge.lean`
only restates it in the board's form.

`Submission/ThreeSatStatement.lean` is the verifier's `challenges/3sat/Statement.lean` with one
change: its first line (`import SubexponentialSATDefinitions`) is replaced by the imports of the
OpenAI modules that define the same names.
-/

theorem Race.bound : BigOSpeedrun.ThreeSat.SolvedInTime ((1 : ℚ) / 2) :=
  BigOSpeedrun.ThreeSat.Bridge.solvedInTime_half
