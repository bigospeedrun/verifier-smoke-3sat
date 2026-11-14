import OAI.Algorithms.SubexponentialSAT.Main
import Submission.ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
Big O Speedrun verifier smoke fixture (not part of openai/math).

This file is ours (Big O Speedrun maintainers). It derives the 3-SAT board target
`BigOSpeedrun.ThreeSat.SolvedInTime (1 / 2)` from OpenAI's theorem
`OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat` with `k = 3`.
The mathematics and the machine are OpenAI's; this file only changes the form of the
statement:

1. a trace of `locatedStep` gives a trace of `PrimitiveMachine.step` (the monitor keeps the
   configuration);
2. `0 < SAT.count F` holds exactly when some assignment satisfies `F`;
3. for every `0 ≤ β < 1/2`, `A · runtimeScale n ≤ n / (log₂(n + 2))^β` for all large `n`;
   a constant `K` covers the finitely many small `n`.
-/

namespace BigOSpeedrun.ThreeSat.Bridge

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Filter Asymptotics

/-- The monitor of a located configuration keeps the configuration it is given. -/
theorem monitor_config {machine : Computation.PrimitiveMachine} (c : LocatedCfg machine)
    (cfg : machine.Cfg) : (c.monitor cfg).config = cfg := by
  unfold LocatedCfg.monitor
  cases c.config.state with
  | inl _ => rfl
  | inr q =>
    simp only [Sum.elim_inr]
    cases machine.transition q (c.config.tapes (machine.scan q)).head <;> rfl

/-- A located trace projects to a trace of the machine. -/
theorem trace_config {machine : Computation.PrimitiveMachine} :
    ∀ {t : ℕ} {a b : LocatedCfg machine},
      Computation.Trace (locatedStep machine) t a b →
        Computation.Trace machine.step t a.config b.config := by
  intro t a b h
  induction h with
  | refl a => exact Computation.Trace.refl _
  | @cons n a b c hstep _ ih =>
    unfold locatedStep at hstep
    cases hs : machine.step a.config with
    | none => simp [hs] at hstep
    | some cfg =>
      rw [hs, Option.map_some] at hstep
      have hb : b.config = cfg := by
        rw [← Option.some_injective _ hstep]
        exact monitor_config a cfg
      exact Computation.Trace.cons (hs.trans (congrArg some hb.symm)) ih

theorem count_pos_iff {n : ℕ} (F : SAT.CNF (Fin n)) :
    decide (0 < SAT.count F) = true ↔ Satisfiable F := by
  simp [SAT.count, SAT.satisfyingAssignments, Finset.card_pos, Finset.filter_nonempty_iff,
    Satisfiable]

theorem half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  linarith

theorem one_le_logb (n : ℕ) : 1 ≤ Real.logb 2 ((n : ℝ) + 2) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  simp

/-- For `0 ≤ β < 1/2` the OpenAI exponent `A · runtimeScale n` is eventually at most
`n / (log₂(n + 2))^β`. -/
theorem scale_eventually_le {A β : ℝ} (hA : 0 < A) (hβ0 : 0 ≤ β) (hβ : β < 1 / 2) :
    ∃ N : ℕ, ∀ n ≥ N,
      A * SqrtLog.Statement.runtimeScale n ≤ (n : ℝ) / (Real.logb 2 ((n : ℝ) + 2)) ^ β := by
  set δ := 1 / 2 - β with hδdef
  have hδ : 0 < δ := by linarith
  have ho := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hδ).bound (c := 1 / (2 * A)) (by positivity)
  have hlim : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 16)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right _ 16 tendsto_natCast_atTop_atTop)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (ho.and (eventually_gt_atTop 0)))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hbound, hy⟩ := hN n hn
  set y := Real.log ((n : ℝ) + 16) with hydef
  set L := Real.logb 2 ((n : ℝ) + 2) with hLdef
  have hL1 : 1 ≤ L := one_le_logb n
  have hLb : 0 < L ^ β := Real.rpow_pos_of_pos (by linarith) _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `L ≤ y / log 2`, hence `L^β ≤ 2 · y^β`.
  have hLy : L ≤ y / Real.log 2 := by
    rw [hLdef, Real.logb]
    apply div_le_div_of_nonneg_right _ hlog2.le
    exact Real.log_le_log (by positivity) (by linarith)
  have hLyβ : L ^ β ≤ 2 * y ^ β := by
    calc L ^ β ≤ (y / Real.log 2) ^ β := Real.rpow_le_rpow (by linarith) hLy hβ0
      _ = y ^ β / Real.log 2 ^ β := Real.div_rpow hy.le hlog2.le β
      _ ≤ y ^ β / (1 / 2) := by
          apply div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) (by norm_num)
          calc (1 : ℝ) / 2 ≤ Real.log 2 := half_le_log_two
            _ = Real.log 2 ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ Real.log 2 ^ β := Real.rpow_le_rpow_of_exponent_ge hlog2
                (by have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith)
                (by linarith)
      _ = 2 * y ^ β := by ring
  -- `log y ^ 2 ≤ y^δ / (2A)`.
  have hu : Real.log y ^ 2 ≤ 1 / (2 * A) * y ^ δ := by
    have := hbound
    simp only [Real.rpow_two, Real.norm_eq_abs] at this
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (Real.rpow_nonneg hy.le _)] at this
    exact this
  have hsqrt : Real.sqrt y = y ^ δ * y ^ β := by
    rw [← Real.rpow_add hy, hδdef, sub_add_cancel, Real.sqrt_eq_rpow]
  have hsq : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hkey : A * Real.log y ^ 2 * L ^ β ≤ Real.sqrt y := by
    calc A * Real.log y ^ 2 * L ^ β ≤ A * Real.log y ^ 2 * (2 * y ^ β) :=
          mul_le_mul_of_nonneg_left hLyβ (by positivity)
      _ = 2 * A * Real.log y ^ 2 * y ^ β := by ring
      _ ≤ 2 * A * (1 / (2 * A) * y ^ δ) * y ^ β := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy.le _)
          exact mul_le_mul_of_nonneg_left hu (by positivity)
      _ = y ^ δ * y ^ β := by field_simp
      _ = Real.sqrt y := hsqrt.symm
  have hfac : A * Real.log y ^ 2 / Real.sqrt y ≤ 1 / L ^ β := by
    rw [div_le_div_iff₀ hsq hLb]
    linarith
  unfold SqrtLog.Statement.runtimeScale
  rw [← hydef]
  calc A * ((n : ℝ) * Real.log y ^ 2 / Real.sqrt y)
        = (n : ℝ) * (A * Real.log y ^ 2 / Real.sqrt y) := by ring
    _ ≤ (n : ℝ) * (1 / L ^ β) := mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg n)
    _ = (n : ℝ) / L ^ β := by ring

/-- For every `β < 1/2` one constant `K` turns the OpenAI time bound into the board's form. -/
theorem exists_constant {C A β : ℝ} (hC : 0 < C) (hA : 0 < A) (hβ : β < 1 / 2) :
    ∃ K : ℕ, ∀ n : ℕ,
      C * (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n) ≤
        (K : ℝ) * (2 : ℝ) ^ ((n : ℝ) / (Real.logb 2 ((n : ℝ) + 2)) ^ β) := by
  set β' := max β 0
  obtain ⟨N, hN⟩ := scale_eventually_le hA (le_max_right β 0) (max_lt hβ (by norm_num))
  set M : ℝ := (∑ n ∈ Finset.range N, (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n)) + 1
  have hM1 : 1 ≤ M := by
    have : 0 ≤ ∑ n ∈ Finset.range N, (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n) :=
      Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (by norm_num) _
    linarith
  refine ⟨⌈C * M⌉₊, fun n => ?_⟩
  have hK : C * M ≤ (⌈C * M⌉₊ : ℝ) := Nat.le_ceil _
  have hL1 : 1 ≤ Real.logb 2 ((n : ℝ) + 2) := one_le_logb n
  have hexp0 : 0 ≤ (n : ℝ) / (Real.logb 2 ((n : ℝ) + 2)) ^ β :=
    div_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg (by linarith) _)
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / (Real.logb 2 ((n : ℝ) + 2)) ^ β) :=
    Real.one_le_rpow (by norm_num) hexp0
  by_cases hn : n < N
  · have hterm : (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n) ≤ M := by
      have := Finset.single_le_sum (f := fun n => (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n))
        (fun _ _ => Real.rpow_nonneg (by norm_num) _) (Finset.mem_range.mpr hn)
      linarith
    calc C * (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n) ≤ C * M :=
          mul_le_mul_of_nonneg_left hterm hC.le
      _ ≤ (⌈C * M⌉₊ : ℝ) := hK
      _ = (⌈C * M⌉₊ : ℝ) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg _)
  · have hle := hN n (by omega)
    have hpow : (Real.logb 2 ((n : ℝ) + 2)) ^ β ≤ (Real.logb 2 ((n : ℝ) + 2)) ^ β' :=
      Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left β 0)
    have hdiv : (n : ℝ) / (Real.logb 2 ((n : ℝ) + 2)) ^ β' ≤
        (n : ℝ) / (Real.logb 2 ((n : ℝ) + 2)) ^ β :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg n)
        (Real.rpow_pos_of_pos (by linarith) _) hpow
    have h2 : (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n) ≤
        (2 : ℝ) ^ ((n : ℝ) / (Real.logb 2 ((n : ℝ) + 2)) ^ β) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (hle.trans hdiv)
    have hCK : C ≤ (⌈C * M⌉₊ : ℝ) := by
      have : C ≤ C * M := le_mul_of_one_le_right hC.le hM1
      linarith
    exact mul_le_mul hCK h2 (Real.rpow_nonneg (by norm_num) _) (Nat.cast_nonneg _)

theorem solvedInTime_half : SolvedInTime ((1 : ℚ) / 2) := by
  obtain ⟨machine, _countTape, _answerTape, C, A, _S, d, _e, hC, hA, _hS, _hd, _he, hrun⟩ :=
    exact_count_and_sat 3 (by norm_num)
  refine ⟨machine, d, fun ε hε => ?_⟩
  have hβ : (((1 : ℚ) / 2 : ℚ) : ℝ) - (ε : ℝ) < 1 / 2 := by
    have : (0 : ℝ) < ε := by exact_mod_cast hε
    push_cast
    linarith
  obtain ⟨K, hK⟩ := exists_constant hC hA hβ
  refine ⟨K, fun n F hw => ?_⟩
  obtain ⟨time, final, htrace, _hcount, _hanswer, hstate, _hdecode, _hlength, htime, _hspace⟩ :=
    hrun n F hw
  refine ⟨time, decide (0 < SAT.count F), count_pos_iff F,
    ⟨final.config, trace_config htrace, hstate⟩, ?_⟩
  refine htime.trans ?_
  unfold SqrtLog.Statement.runtimeBound timeBound
  have hpoly : 0 ≤ ((Encoding.formulaBitLength F : ℝ) + 1) ^ d := by positivity
  calc C * ((Encoding.formulaBitLength F : ℝ) + 1) ^ d *
        (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n)
      = ((Encoding.formulaBitLength F : ℝ) + 1) ^ d *
          (C * (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n)) := by ring
    _ ≤ ((Encoding.formulaBitLength F : ℝ) + 1) ^ d *
          ((K : ℝ) * (2 : ℝ) ^ ((n : ℝ) /
            (Real.logb 2 ((n : ℝ) + 2)) ^ ((((1 : ℚ) / 2 : ℚ) : ℝ) - (ε : ℝ)))) :=
        mul_le_mul_of_nonneg_left (hK n) hpoly
    _ = _ := by ring

end BigOSpeedrun.ThreeSat.Bridge
