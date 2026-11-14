import Submission.ThreeSatStatement

/-! Maintainer smoke case (control): the statement copy, Race.bound by sorry (must fail on sorryAx; with bound 3/5 it must fail at compare). -/

theorem Race.bound : BigOSpeedrun.ThreeSat.SolvedInTime ((1 : ℚ) / 2) := by
  sorry
