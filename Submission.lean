import Submission.ThreeSatStatement

/-! Maintainer smoke case (m6-def): SolvedInTime redefined as True, Race.bound without sorry (must fail at compare, statement_mismatch on the definition). -/

theorem Race.bound : BigOSpeedrun.ThreeSat.SolvedInTime ((1 : ℚ) / 2) := trivial
