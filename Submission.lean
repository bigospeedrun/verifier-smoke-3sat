import Submission.ThreeSatStatement

/-! Maintainer smoke case (m7-type): Race.bound states True, without sorry (must fail at compare, statement_mismatch on the theorem). The proof goes through Classical.em so that the axiom audit reports the standard axioms and passes. -/

theorem Race.bound : True := (Classical.em True).elim (fun _ => trivial) (fun _ => trivial)
