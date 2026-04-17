import PrimeNumberTheoremAnd.RamanujanCalculations
import LeanCert.Tactic.IntervalAuto

namespace Ramanujan

open Real Set MeasureTheory intervalIntegral

namespace FKS14Calculations

noncomputable def styleVal (y : ℝ) : ℝ :=
  (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
    (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
    exp (-(2 : ℝ) * sqrt (y / 5.5666305))

noncomputable def styleUVal (u : ℝ) : ℝ :=
  (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
    u ^ (13 : ℕ) * exp (-(2 : ℝ) * u)

theorem styleVal_bound {L U C : ℝ}
    (haux : ∀ y ∈ Set.Icc L U, styleVal y ≤ C) :
    ∀ y ∈ Set.Icc L U, styleVal y ≤ C := haux

theorem styleUVal_bound {L U C : ℝ}
    (haux : ∀ u ∈ Set.Icc L U, styleUVal u ≤ C) :
    ∀ u ∈ Set.Icc L U, styleUVal u ≤ C := haux

theorem styleVal_nonneg (y : ℝ) : 0 ≤ styleVal y := by
  unfold styleVal
  positivity

theorem log_two_lt_one : log (2 : ℝ) < 1 :=
  (show ∀ y ∈ Set.Icc (2 : ℝ) 2, log y < (1 : ℝ) by interval_bound 20)
    2 ⟨le_refl _, le_refl _⟩

theorem exp_one_gt_two : (2 : ℝ) < exp (1 : ℝ) :=
  (show ∀ y ∈ Set.Icc (1 : ℝ) 1, (2 : ℝ) < exp y by interval_bound 20)
    1 ⟨le_refl _, le_refl _⟩

theorem formula_eq_style (z : ℝ) (hz : 1 < z) :
    (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z = styleVal (log z) := by
  let R : ℝ := 5.5666305
  let u : ℝ := sqrt (log z / R)
  have hbase_pos : 0 < log z / R := by
    dsimp [R]
    positivity [log_pos hz]
  have hu_sq : u ^ (2 : ℕ) = log z / R := by
    dsimp [u]
    simpa [pow_two] using sq_sqrt hbase_pos.le
  have hsqrt : (log z / R) ^ ((1 : ℝ) / 2 : ℝ) = u := by
    dsimp [u]
    rw [show ((1 : ℝ) / 2 : ℝ) = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  have hpow32 : (log z / R) ^ (3 / 2 : ℝ) = u ^ (3 : ℕ) := by
    rw [show (3 / 2 : ℝ) = (1 : ℝ) + ((1 : ℝ) / 2 : ℝ) by norm_num, Real.rpow_add hbase_pos,
      Real.rpow_one, hsqrt, ← hu_sq]
    ring
  have hlog_eq : log z = R * u ^ (2 : ℕ) := by
    dsimp [R] at hu_sq ⊢
    calc
      log z = (log z / 5.5666305) * 5.5666305 := by
        field_simp
      _ = u ^ (2 : ℕ) * 5.5666305 := by rw [← hu_sq]
      _ = 5.5666305 * u ^ (2 : ℕ) := by ring
  calc
    (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z
        = (log z) ^ 5 * ((121.0961 : ℝ) * (log z / R) ^ (3 / 2 : ℝ) *
            exp (-(2 : ℝ) * u)) := by
            unfold admissible_bound
            rw [hsqrt]
    _ = (121.0961 : ℝ) * (log z) ^ 5 * u ^ (3 : ℕ) * exp (-(2 : ℝ) * u) := by
      rw [hpow32]
      ring
    _ = (121.0961 : ℝ) * R ^ (5 : ℕ) * u ^ (13 : ℕ) * exp (-(2 : ℝ) * u) := by
      rw [hlog_eq]
      ring_nf
    _ = styleVal (log z) := by
      unfold styleVal
      dsimp [R, u]

theorem a_nonneg_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z)
    {z : ℝ} (hz : z ≥ 2) :
    0 ≤ a z := by
  rw [ha_eq_admissible_ge_two hz, formula_eq_style z (by linarith)]
  exact styleVal_nonneg (log z)

theorem formula_eq_admissible (z : ℝ) (hz : 1 < z) :
    (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z
      = admissible_bound ((121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ)) (13 / 2) 2 5.5666305 z := by
  have hdiv : 0 < log z / 5.5666305 := by
    positivity [log_pos hz]
  unfold admissible_bound
  have hpow : (log z) ^ (5 : ℕ) = (5.5666305 : ℝ) ^ (5 : ℕ) * (log z / 5.5666305) ^ (5 : ℕ) := by
    rw [show log z = 5.5666305 * (log z / 5.5666305) by field_simp]
    ring
  have hrpow :
      (log z / 5.5666305) ^ (5 : ℕ) * (log z / 5.5666305) ^ (3 / 2 : ℝ)
        = (log z / 5.5666305) ^ (13 / 2 : ℝ) := by
    rw [← rpow_natCast (log z / 5.5666305) 5, ← rpow_add hdiv]
    norm_num
  rw [hpow]
  conv_lhs =>
    rw [show ∀ (u v w r s : ℝ), u * v * (w * r * s) = w * u * (v * r) * s from by
      intro u v w r s
      ring]
  rw [hrpow]

theorem styleVal_tail_antitone : AntitoneOn styleVal (Set.Ici (236 : ℝ)) := by
  intro y hy y' hy' hyy'
  have hy_exp : 1 < exp y := by
    have : (1 : ℝ) < exp (236 : ℝ) := by
      have h : (1 : ℝ) < exp 1 := (Real.one_lt_exp_iff).2 (by norm_num)
      exact lt_of_lt_of_le h (exp_le_exp.mpr (by norm_num))
    exact lt_of_lt_of_le this (exp_le_exp.mpr (Set.mem_Ici.mp hy))
  have hy'_exp : 1 < exp y' := by
    have : (1 : ℝ) < exp (236 : ℝ) := by
      have h : (1 : ℝ) < exp 1 := (Real.one_lt_exp_iff).2 (by norm_num)
      exact lt_of_lt_of_le h (exp_le_exp.mpr (by norm_num))
    exact lt_of_lt_of_le this (exp_le_exp.mpr (Set.mem_Ici.mp hy'))
  calc
    styleVal y' = (y') ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 (exp y') := by
      symm
      simpa [log_exp] using formula_eq_style (exp y') hy'_exp
    _ = admissible_bound ((121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ)) (13 / 2) 2 5.5666305 (exp y') := by
      simpa [log_exp] using formula_eq_admissible (exp y') hy'_exp
    _ ≤ admissible_bound ((121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ)) (13 / 2) 2 5.5666305 (exp y) := 
      admissible_bound.mono
        ((121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ)) (13 / 2) 2 5.5666305
        (by positivity) (by positivity) (by positivity) (by positivity)
        (Set.mem_Ici.mpr <| by
          have hth : exp ((5.5666305 : ℝ) * (2 * (13 / 2 : ℝ) / 2) ^ 2) ≤ exp (236 : ℝ) := by
            exact exp_le_exp.mpr (by norm_num)
          exact le_trans hth (exp_le_exp.mpr (Set.mem_Ici.mp hy)))
        (Set.mem_Ici.mpr <| by
          have hth : exp ((5.5666305 : ℝ) * (2 * (13 / 2 : ℝ) / 2) ^ 2) ≤ exp (236 : ℝ) := by
            exact exp_le_exp.mpr (by norm_num)
          exact le_trans hth (exp_le_exp.mpr (Set.mem_Ici.mp hy')))
        (exp_le_exp.mpr hyy')
    _ = y ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 (exp y) := by
      simpa [log_exp] using (formula_eq_admissible (exp y) hy_exp).symm
    _ = styleVal y := by
      simpa [log_exp] using formula_eq_style (exp y) hy_exp

theorem a_mono_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z) :
    AntitoneOn a (Set.Ici (exp (236 : ℝ))) := by
  intro x hx y hy hxy
  have hx2 : 2 ≤ x := by
    have : 2 ≤ exp (236 : ℝ) := by
      have h : (2 : ℝ) ≤ exp 1 := le_of_lt exp_one_gt_two
      exact le_trans h (exp_le_exp.mpr (by norm_num))
    exact le_trans this hx
  have hy2 : 2 ≤ y := by
    exact le_trans hx2 hxy
  rw [ha_eq_admissible_ge_two hx2, ha_eq_admissible_ge_two hy2,
    formula_eq_admissible x (by linarith), formula_eq_admissible y (by linarith)]
  exact admissible_bound.mono _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)
    (Set.mem_Ici.mpr <| le_trans (exp_le_exp.mpr (by norm_num :
      (5.5666305 : ℝ) * (2 * (13 / 2 : ℝ) / 2) ^ 2 ≤ 236)) hx)
    (Set.mem_Ici.mpr <| le_trans (exp_le_exp.mpr (by norm_num :
      (5.5666305 : ℝ) * (2 * (13 / 2 : ℝ) / 2) ^ 2 ≤ 236)) hy)
    hxy

theorem a_exp_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z)
    {L C : ℝ}
    (hL : log 2 ≤ L)
    (haux : ∀ y ∈ Set.Icc L L, styleVal y ≤ C) :
    a (exp L) ≤ C := by
  have h2 : 2 ≤ exp L := by
    calc
      (2 : ℝ) = exp (log 2) := by rw [exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ exp L := exp_le_exp.mpr hL
  rw [ha_eq_admissible_ge_two (z := exp L) h2, formula_eq_style (exp L) (by
    have h2' : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le h2' h2), log_exp]
  exact haux L ⟨le_rfl, le_rfl⟩

theorem styleVal_bound_3120_1300 :
    ∀ y ∈ Set.Icc (3120 : ℝ) 3120, styleVal y ≤ (1300 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (3120 : ℝ) 3120,
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (1300 : ℝ) := by
    interval_bound 20
  simpa [styleVal] using haux

theorem styleVal_bound_2271_172279 :
    ∀ y ∈ Set.Icc (2271 : ℝ) 2271, styleVal y ≤ (172279 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (2271 : ℝ) 2271,
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (172279 : ℝ) := by
    interval_bound 20
  simpa [styleVal] using haux

theorem styleVal_bound_2272_171243 :
    ∀ y ∈ Set.Icc (2272 : ℝ) 2272, styleVal y ≤ (171243 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (2272 : ℝ) 2272,
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (171243 : ℝ) := by
    interval_bound 20
  simpa [styleVal] using haux

theorem styleVal_bound_2273_170214 :
    ∀ y ∈ Set.Icc (2273 : ℝ) 2273, styleVal y ≤ (170214 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (2273 : ℝ) 2273,
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (170214 : ℝ) := by
    interval_bound 20
  simpa [styleVal] using haux

theorem styleVal_bound_770_3250000000 :
    ∀ y ∈ Set.Icc (770 : ℝ) 770, styleVal y ≤ (3250000000 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (770 : ℝ) 770,
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (3250000000 : ℝ) := by
    interval_bound 20
  simpa [styleVal] using haux

theorem styleVal_bound_792_2793000000 :
    ∀ y ∈ Set.Icc (792 : ℝ) 792, styleVal y ≤ (2793000000 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (792 : ℝ) 792,
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (2793000000 : ℝ) := by
    interval_bound 20
  simpa [styleVal] using haux

theorem styleVal_bound_793_2774000000 :
    ∀ y ∈ Set.Icc (793 : ℝ) 793, styleVal y ≤ (2774000000 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (793 : ℝ) 793,
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (2774000000 : ℝ) := by
    interval_bound 20
  simpa [styleVal] using haux

theorem styleVal_bound_3157_1060 :
    ∀ y ∈ Set.Icc (3157 : ℝ) 3157, styleVal y ≤ (1060 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (3157 : ℝ) 3157,
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (1060 : ℝ) := by
    interval_bound 20
  simpa [styleVal] using haux

theorem styleVal_bound_3158_1054 :
    ∀ y ∈ Set.Icc (3158 : ℝ) 3158, styleVal y ≤ (1054 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (3158 : ℝ) 3158,
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (1054 : ℝ) := by
    interval_bound 20
  simpa [styleVal] using haux

theorem styleVal_bound_3159_1048 :
    ∀ y ∈ Set.Icc (3159 : ℝ) 3159, styleVal y ≤ (1048 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (3159 : ℝ) 3159,
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (1048 : ℝ) := by
    interval_bound 20
  simpa [styleVal] using haux

theorem styleUVal_bound_24_huge :
    ∀ u ∈ Set.Icc (0 : ℝ) 24, styleUVal u ≤ (1e24 : ℝ) := by
  intro u hu
  have hu_nonneg : 0 ≤ u := hu.1
  have hu_pow : u ^ (13 : ℕ) ≤ (24 : ℝ) ^ (13 : ℕ) := pow_le_pow_left₀ hu_nonneg hu.2 13
  have hexp_le : exp (-(2 : ℝ) * u) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [hu_nonneg])
  unfold styleUVal
  calc
    (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) * u ^ (13 : ℕ) * exp (-(2 : ℝ) * u)
        ≤ (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) * (24 : ℝ) ^ (13 : ℕ) * 1 := by
          gcongr
    _ ≤ (1e24 : ℝ) := by
      norm_num

theorem styleVal_bound_log2_50_huge :
    ∀ y ∈ Set.Icc (log 2) (50 : ℝ), styleVal y ≤ (100000000000000 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc ((69 / 100 : ℝ)) (50 : ℝ),
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (100000000000000 : ℝ) := by
    interval_bound 20
  intro y hy
  have hy' : y ∈ Set.Icc ((69 / 100 : ℝ)) (50 : ℝ) := by
    constructor
    · have : ((69 / 100 : ℝ)) ≤ log 2 := by
        linarith [Real.log_two_gt_d9]
      exact le_trans this hy.1
    · exact hy.2
  simpa [styleVal] using haux y hy'

theorem styleVal_bound_50_236_huge :
    ∀ y ∈ Set.Icc (50 : ℝ) (236 : ℝ), styleVal y ≤ (100000000000000 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (50 : ℝ) (236 : ℝ),
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (100000000000000 : ℝ) := by
    interval_bound 20
  simpa [styleVal] using haux

theorem styleVal_bound_236_peak :
    ∀ y ∈ Set.Icc (236 : ℝ) (236 : ℝ), styleVal y ≤ (60000000000 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (236 : ℝ) (236 : ℝ),
      (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ) *
        (sqrt (y / 5.5666305)) ^ (13 : ℕ) *
        exp (-(2 : ℝ) * sqrt (y / 5.5666305)) ≤ (60000000000 : ℝ) := by
    interval_bound 20
  simpa [styleVal] using haux

theorem styleVal_bound_3120_huge :
    ∀ y ∈ Set.Icc (log 2) (3120 : ℝ), styleVal y ≤ (100000000000000 : ℝ) := by
  intro y hy
  by_cases h50 : y ≤ (50 : ℝ)
  · exact styleVal_bound_log2_50_huge y ⟨hy.1, h50⟩
  · by_cases h236 : y ≤ (236 : ℝ)
    · exact styleVal_bound_50_236_huge y ⟨le_of_not_ge h50, h236⟩
    · have hy236 : (236 : ℝ) ≤ y := le_of_not_ge h236
      have htail : styleVal y ≤ styleVal (236 : ℝ) :=
        styleVal_tail_antitone (Set.mem_Ici.mpr (le_rfl : (236 : ℝ) ≤ 236))
          (Set.mem_Ici.mpr hy236) hy236
      have hpeak : styleVal (236 : ℝ) ≤ (60000000000 : ℝ) :=
        styleVal_bound_236_peak 236 ⟨le_rfl, le_rfl⟩
      exact le_trans htail (by linarith)

theorem a_3120_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z) :
    a (exp (3120 : ℝ)) ≤ (1300 : ℝ) := by
  have hL : log 2 ≤ (3120 : ℝ) := by
    linarith [log_two_lt_one]
  exact a_exp_upper_of (a := a) ha_eq_admissible_ge_two hL styleVal_bound_3120_1300

theorem a_2271_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z) :
    a (exp (2271 : ℝ)) ≤ (172279 : ℝ) := by
  have hL : log 2 ≤ (2271 : ℝ) := by
    linarith [log_two_lt_one]
  exact a_exp_upper_of (a := a) ha_eq_admissible_ge_two hL styleVal_bound_2271_172279

theorem a_2272_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z) :
    a (exp (2272 : ℝ)) ≤ (171243 : ℝ) := by
  have hL : log 2 ≤ (2272 : ℝ) := by
    linarith [log_two_lt_one]
  exact a_exp_upper_of (a := a) ha_eq_admissible_ge_two hL styleVal_bound_2272_171243

theorem a_2273_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z) :
    a (exp (2273 : ℝ)) ≤ (170214 : ℝ) := by
  have hL : log 2 ≤ (2273 : ℝ) := by
    linarith [log_two_lt_one]
  exact a_exp_upper_of (a := a) ha_eq_admissible_ge_two hL styleVal_bound_2273_170214

theorem a_770_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z) :
    a (exp (770 : ℝ)) ≤ (3250000000 : ℝ) := by
  have hL : log 2 ≤ (770 : ℝ) := by
    linarith [log_two_lt_one]
  exact a_exp_upper_of (a := a) ha_eq_admissible_ge_two hL styleVal_bound_770_3250000000

theorem a_792_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z) :
    a (exp (792 : ℝ)) ≤ (2793000000 : ℝ) := by
  have hL : log 2 ≤ (792 : ℝ) := by
    linarith [log_two_lt_one]
  exact a_exp_upper_of (a := a) ha_eq_admissible_ge_two hL styleVal_bound_792_2793000000

theorem a_793_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z) :
    a (exp (793 : ℝ)) ≤ (2774000000 : ℝ) := by
  have hL : log 2 ≤ (793 : ℝ) := by
    linarith [log_two_lt_one]
  exact a_exp_upper_of (a := a) ha_eq_admissible_ge_two hL styleVal_bound_793_2774000000

theorem a_3157_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z) :
    a (exp (3157 : ℝ)) ≤ (1060 : ℝ) := by
  have hL : log 2 ≤ (3157 : ℝ) := by
    linarith [log_two_lt_one]
  exact a_exp_upper_of (a := a) ha_eq_admissible_ge_two hL styleVal_bound_3157_1060

theorem a_3158_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z) :
    a (exp (3158 : ℝ)) ≤ (1054 : ℝ) := by
  have hL : log 2 ≤ (3158 : ℝ) := by
    linarith [log_two_lt_one]
  exact a_exp_upper_of (a := a) ha_eq_admissible_ge_two hL styleVal_bound_3158_1054

theorem a_3159_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z) :
    a (exp (3159 : ℝ)) ≤ (1048 : ℝ) := by
  have hL : log 2 ≤ (3159 : ℝ) := by
    linarith [log_two_lt_one]
  exact a_exp_upper_of (a := a) ha_eq_admissible_ge_two hL styleVal_bound_3159_1048

theorem a_low_huge_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z)
    {t : ℝ} (ht : t ∈ Set.Icc 2 (exp (3120 : ℝ))) :
    a t ≤ (100000000000000 : ℝ) := by
  have ht1 : (1 : ℝ) < t := by linarith [ht.1]
  rw [ha_eq_admissible_ge_two ht.1, formula_eq_style t ht1]
  have hlog_mem : log t ∈ Set.Icc (log 2) (3120 : ℝ) := by
    constructor
    · exact log_le_log (by positivity : (0 : ℝ) < 2) ht.1
    · have ht_pos : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
      have h := log_le_log ht_pos ht.2
      simpa [log_exp] using h
  exact styleVal_bound_3120_huge (log t) hlog_mem

theorem exp_neg38_small :
    exp (-(38 : ℝ)) ≤ (1e-16 : ℝ) :=
  (show ∀ z ∈ Set.Icc (38 : ℝ) 38, exp (-z) ≤ (1e-16 : ℝ) by interval_bound 20)
    38 ⟨le_refl _, le_refl _⟩

theorem exp_neg37_small :
    exp (-(37 : ℝ)) ≤ (1e-16 : ℝ) :=
  (show ∀ z ∈ Set.Icc (37 : ℝ) 37, exp (-z) ≤ (1e-16 : ℝ) by interval_bound 20)
    37 ⟨le_refl _, le_refl _⟩

theorem exp_neg1598_small :
    exp (-(1598 : ℝ)) ≤ (1e-50 : ℝ) :=
  (show ∀ z ∈ Set.Icc (1598 : ℝ) 1598, exp (-z) ≤ (1e-50 : ℝ) by interval_bound 20)
    1598 ⟨le_refl _, le_refl _⟩

theorem exp_neg1597_small :
    exp (-(1597 : ℝ)) ≤ (1e-50 : ℝ) :=
  (show ∀ z ∈ Set.Icc (1597 : ℝ) 1597, exp (-z) ≤ (1e-50 : ℝ) by interval_bound 20)
    1597 ⟨le_refl _, le_refl _⟩

theorem low_contrib_le_one_tenth_3157 :
    (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) *
      (exp (-(37 : ℝ)) / (3120 : ℝ) ^ 7
        + 7 * (exp (-(1597 : ℝ)) / (log 2) ^ 8
          + (2 : ℝ) ^ 8 * exp (-(37 : ℝ)) / (3120 : ℝ) ^ 8))
      ≤ (1 : ℝ) / 10 := by
  have hAcoeff :
      (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) / (3120 : ℝ) ^ 7 ≤ (50000000000 : ℝ) := by
    norm_num
  have hCcoeff :
      (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * (7 * (2 : ℝ) ^ 8) / (3120 : ℝ) ^ 8
        ≤ (20000000000 : ℝ) := by
    norm_num
  have hBcoeff0 :
      (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 ≤ (1e36 : ℝ) := by
    norm_num
  have hA :
      (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * exp (-(37 : ℝ)) / (3120 : ℝ) ^ 7
        ≤ (1 : ℝ) / 1000 := by
    rw [show (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * exp (-(37 : ℝ)) / (3120 : ℝ) ^ 7
        = ((3157 : ℝ) ^ 6 * (100000000000720 : ℝ) / (3120 : ℝ) ^ 7) * exp (-(37 : ℝ)) by ring]
    exact le_trans
      (mul_le_mul hAcoeff exp_neg37_small (by positivity) (by positivity))
      (by norm_num)
  have hC :
      (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) *
        (7 * (2 : ℝ) ^ 8) * exp (-(37 : ℝ)) / (3120 : ℝ) ^ 8 ≤ (1 : ℝ) / 1000 := by
    rw [show (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) *
          (7 * (2 : ℝ) ^ 8) * exp (-(37 : ℝ)) / (3120 : ℝ) ^ 8
        = ((3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * (7 * (2 : ℝ) ^ 8) /
              (3120 : ℝ) ^ 8) * exp (-(37 : ℝ)) by ring]
    exact le_trans
      (mul_le_mul hCcoeff exp_neg37_small (by positivity) (by positivity))
      (by norm_num)
  have hB :
      (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 *
        (exp (-(1597 : ℝ)) / (log 2) ^ 8) ≤ (1 : ℝ) / 1000 := by
    have hBcoeff :
        (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 / (log 2) ^ 8 ≤ (1e39 : ℝ) := by
      rw [show (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 / (log 2) ^ 8
          = ((3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7) * (1 / (log 2) ^ 8) by ring]
      nlinarith [inv_log2_pow8_le_1000, hBcoeff0]
    rw [show (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 *
          (exp (-(1597 : ℝ)) / (log 2) ^ 8)
        = ((3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 / (log 2) ^ 8) *
            exp (-(1597 : ℝ)) by ring]
    exact le_trans
      (mul_le_mul hBcoeff exp_neg1597_small (by positivity) (by positivity))
      (by norm_num)
  have hrewrite :
      (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) *
        (exp (-(37 : ℝ)) / (3120 : ℝ) ^ 7
          + 7 * (exp (-(1597 : ℝ)) / (log 2) ^ 8
            + (2 : ℝ) ^ 8 * exp (-(37 : ℝ)) / (3120 : ℝ) ^ 8))
      = (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * exp (-(37 : ℝ)) / (3120 : ℝ) ^ 7
        + (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 *
            (exp (-(1597 : ℝ)) / (log 2) ^ 8)
        + (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) *
            (7 * (2 : ℝ) ^ 8) * exp (-(37 : ℝ)) / (3120 : ℝ) ^ 8 := by
    ring
  rw [hrewrite]
  nlinarith [hA, hB, hC]

theorem low_contrib_raw_le_one_tenth_3157 :
    (3157 : ℝ) ^ 6 / exp (3157 : ℝ) *
      ((100000000000720 : ℝ) *
        (exp (3120 : ℝ) / (3120 : ℝ) ^ 7
          + 7 *
            (sqrt (exp (3120 : ℝ)) / (log 2) ^ 8
              + (2 : ℝ) ^ 8 * exp (3120 : ℝ) / (3120 : ℝ) ^ 8)))
      ≤ (1 : ℝ) / 10 := by
  have h37 : exp (3120 : ℝ) / exp (3157 : ℝ) = exp (-(37 : ℝ)) := by
    have h := (exp_sub (3120 : ℝ) (3157 : ℝ)).symm
    simpa [show (3120 : ℝ) - 3157 = (-(37 : ℝ)) by norm_num] using h
  have h1597 : exp (1560 : ℝ) / exp (3157 : ℝ) = exp (-(1597 : ℝ)) := by
    have h := (exp_sub (1560 : ℝ) (3157 : ℝ)).symm
    simpa [show (1560 : ℝ) - 3157 = (-(1597 : ℝ)) by norm_num] using h
  have hsqrt3120 : sqrt (exp (3120 : ℝ)) = exp (1560 : ℝ) := by
    rw [show (3120 : ℝ) = 1560 + 1560 by norm_num, exp_add, sqrt_mul (by positivity)]
    nlinarith [Real.sq_sqrt (show 0 ≤ exp (1560 : ℝ) by positivity)]
  rw [hsqrt3120]
  have hrewrite :
      (3157 : ℝ) ^ 6 / exp (3157 : ℝ) *
          ((100000000000720 : ℝ) *
            (exp (3120 : ℝ) / (3120 : ℝ) ^ 7
              + 7 *
                (exp (1560 : ℝ) / (log 2) ^ 8
                  + (2 : ℝ) ^ 8 * exp (3120 : ℝ) / (3120 : ℝ) ^ 8)))
        = (3157 : ℝ) ^ 6 * (100000000000720 : ℝ) *
            (exp (-(37 : ℝ)) / (3120 : ℝ) ^ 7
              + 7 * (exp (-(1597 : ℝ)) / (log 2) ^ 8
                + (2 : ℝ) ^ 8 * exp (-(37 : ℝ)) / (3120 : ℝ) ^ 8)) := by
    rw [← h37, ← h1597]
    field_simp
  rw [hrewrite]
  exact low_contrib_le_one_tenth_3157

theorem high_contrib_le_seven_tenths_3157 :
    (2020 : ℝ) * (3157 : ℝ) ^ 6 / (3120 : ℝ) ^ 7 ≤ (7 : ℝ) / 10 := by
  norm_num

theorem exp_8_lt_3157 : exp (8 : ℝ) < (3157 : ℝ) :=
  (show ∀ y ∈ Set.Icc (8 : ℝ) 8, exp y < (3157 : ℝ) by interval_bound 20)
    8 ⟨le_refl _, le_refl _⟩

theorem sqrt_exp_3157 : sqrt (exp (3157 : ℝ)) = exp ((3157 : ℝ) / 2) := by
  rw [show (3157 : ℝ) = (3157 : ℝ) / 2 + (3157 : ℝ) / 2 by ring, exp_add, sqrt_mul (by positivity)]
  nlinarith [Real.sq_sqrt (show 0 ≤ exp ((3157 : ℝ) / 2) by positivity)]

theorem tail_small_3157 :
    7 * (3157 : ℝ) ^ 6 * exp (-((3157 : ℝ) / 2)) / (log 2) ^ 8 ≤ (1 : ℝ) / 1000000 := by
  have h := (show ∀ y ∈ Set.Icc (3157 : ℝ) 3157,
      7 * y ^ 6 * exp (-y / 2) / (log 2) ^ 8 ≤ (1 : ℝ) / 1000000 by
    interval_bound 20) 3157 ⟨le_refl _, le_refl _⟩
  simpa [show (-(3157 : ℝ) / 2) = -((3157 : ℝ) / 2) by ring] using h

theorem low_contrib_le_one_tenth :
    (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) *
      (exp (-(38 : ℝ)) / (3120 : ℝ) ^ 7
        + 7 * (exp (-(1598 : ℝ)) / (log 2) ^ 8
          + (2 : ℝ) ^ 8 * exp (-(38 : ℝ)) / (3120 : ℝ) ^ 8))
      ≤ (1 : ℝ) / 10 := by
  have hAcoeff :
      (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) / (3120 : ℝ) ^ 7 ≤ (50000000000 : ℝ) := by
    norm_num
  have hCcoeff :
      (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * (7 * (2 : ℝ) ^ 8) / (3120 : ℝ) ^ 8
        ≤ (20000000000 : ℝ) := by
    norm_num
  have hBcoeff0 :
      (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 ≤ (1e36 : ℝ) := by
    norm_num
  have hA :
      (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * exp (-(38 : ℝ)) / (3120 : ℝ) ^ 7
        ≤ (1 : ℝ) / 1000 := by
    rw [show (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * exp (-(38 : ℝ)) / (3120 : ℝ) ^ 7
        = ((3158 : ℝ) ^ 6 * (100000000000720 : ℝ) / (3120 : ℝ) ^ 7) * exp (-(38 : ℝ)) by ring]
    exact le_trans
      (mul_le_mul hAcoeff exp_neg38_small (by positivity) (by positivity))
      (by norm_num)
  have hC :
      (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) *
        (7 * (2 : ℝ) ^ 8) * exp (-(38 : ℝ)) / (3120 : ℝ) ^ 8 ≤ (1 : ℝ) / 1000 := by
    rw [show (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) *
          (7 * (2 : ℝ) ^ 8) * exp (-(38 : ℝ)) / (3120 : ℝ) ^ 8
        = ((3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * (7 * (2 : ℝ) ^ 8) /
              (3120 : ℝ) ^ 8) * exp (-(38 : ℝ)) by ring]
    exact le_trans
      (mul_le_mul hCcoeff exp_neg38_small (by positivity) (by positivity))
      (by norm_num)
  have hB :
      (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 *
        (exp (-(1598 : ℝ)) / (log 2) ^ 8) ≤ (1 : ℝ) / 1000 := by
    have hBcoeff :
        (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 / (log 2) ^ 8 ≤ (1e39 : ℝ) := by
      rw [show (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 / (log 2) ^ 8
          = ((3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7) * (1 / (log 2) ^ 8) by ring]
      nlinarith [inv_log2_pow8_le_1000, hBcoeff0]
    rw [show (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 *
          (exp (-(1598 : ℝ)) / (log 2) ^ 8)
        = ((3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 / (log 2) ^ 8) *
            exp (-(1598 : ℝ)) by ring]
    exact le_trans
      (mul_le_mul hBcoeff exp_neg1598_small (by positivity) (by positivity))
      (by norm_num)
  have hrewrite :
      (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) *
        (exp (-(38 : ℝ)) / (3120 : ℝ) ^ 7
          + 7 * (exp (-(1598 : ℝ)) / (log 2) ^ 8
            + (2 : ℝ) ^ 8 * exp (-(38 : ℝ)) / (3120 : ℝ) ^ 8))
      = (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * exp (-(38 : ℝ)) / (3120 : ℝ) ^ 7
        + (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 *
            (exp (-(1598 : ℝ)) / (log 2) ^ 8)
        + (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) *
            (7 * (2 : ℝ) ^ 8) * exp (-(38 : ℝ)) / (3120 : ℝ) ^ 8 := by
    ring
  rw [hrewrite]
  nlinarith [hA, hB, hC]

theorem sqrt_exp_3120 : sqrt (exp (3120 : ℝ)) = exp (1560 : ℝ) := by
  rw [show (3120 : ℝ) = 1560 + 1560 by norm_num, exp_add, sqrt_mul (by positivity)]
  nlinarith [Real.sq_sqrt (show 0 ≤ exp (1560 : ℝ) by positivity)]

theorem low_contrib_raw_le_one_tenth :
    (3158 : ℝ) ^ 6 / exp (3158 : ℝ) *
      ((100000000000720 : ℝ) *
        (exp (3120 : ℝ) / (3120 : ℝ) ^ 7
          + 7 *
            (sqrt (exp (3120 : ℝ)) / (log 2) ^ 8
              + (2 : ℝ) ^ 8 * exp (3120 : ℝ) / (3120 : ℝ) ^ 8)))
      ≤ (1 : ℝ) / 10 := by
  have h38 : exp (3120 : ℝ) / exp (3158 : ℝ) = exp (-(38 : ℝ)) := by
    have h := (exp_sub (3120 : ℝ) (3158 : ℝ)).symm
    simpa [show (3120 : ℝ) - 3158 = (-(38 : ℝ)) by norm_num] using h
  have h1598 : exp (1560 : ℝ) / exp (3158 : ℝ) = exp (-(1598 : ℝ)) := by
    have h := (exp_sub (1560 : ℝ) (3158 : ℝ)).symm
    simpa [show (1560 : ℝ) - 3158 = (-(1598 : ℝ)) by norm_num] using h
  rw [sqrt_exp_3120]
  have hrewrite :
      (3158 : ℝ) ^ 6 / exp (3158 : ℝ) *
          ((100000000000720 : ℝ) *
            (exp (3120 : ℝ) / (3120 : ℝ) ^ 7
              + 7 *
                (exp (1560 : ℝ) / (log 2) ^ 8
                  + (2 : ℝ) ^ 8 * exp (3120 : ℝ) / (3120 : ℝ) ^ 8)))
        = (3158 : ℝ) ^ 6 * (100000000000720 : ℝ) *
            (exp (-(38 : ℝ)) / (3120 : ℝ) ^ 7
              + 7 * (exp (-(1598 : ℝ)) / (log 2) ^ 8
                + (2 : ℝ) ^ 8 * exp (-(38 : ℝ)) / (3120 : ℝ) ^ 8)) := by
    rw [← h38, ← h1598]
    field_simp
  rw [hrewrite]
  exact low_contrib_le_one_tenth

theorem high_contrib_le_seven_tenths :
    (2020 : ℝ) * (3158 : ℝ) ^ 6 / (3120 : ℝ) ^ 7 ≤ (7 : ℝ) / 10 := by
  norm_num

theorem exp_8_lt_3158 : exp (8 : ℝ) < (3158 : ℝ) :=
  (show ∀ y ∈ Set.Icc (8 : ℝ) 8, exp y < (3158 : ℝ) by interval_bound 20)
    8 ⟨le_refl _, le_refl _⟩

theorem sqrt_exp_3158 : sqrt (exp (3158 : ℝ)) = exp (1579 : ℝ) := by
  rw [show (3158 : ℝ) = 1579 + 1579 by norm_num, exp_add, sqrt_mul (by positivity)]
  nlinarith [Real.sq_sqrt (show 0 ≤ exp (1579 : ℝ) by positivity)]

theorem tail_small :
    7 * (3158 : ℝ) ^ 6 * exp (-(1579 : ℝ)) / (log 2) ^ 8 ≤ (1 : ℝ) / 1000000 := by
  have h := (show ∀ y ∈ Set.Icc (3158 : ℝ) 3158,
      7 * y ^ 6 * exp (-y / 2) / (log 2) ^ 8 ≤ (1 : ℝ) / 1000000 by
    interval_bound 20) 3158 ⟨le_refl _, le_refl _⟩
  simpa [show (-(3158 : ℝ) / 2) = -(1579 : ℝ) by ring] using h

theorem B_le_small_of
    {xₐ : ℝ}
    (hxₐ : xₐ = exp (3158 : ℝ))
    (hlogxₐ : log xₐ = (3158 : ℝ)) :
    1 / log xₐ + 7 * 2 ^ 8 / log xₐ ^ 2
      + 7 * log xₐ ^ 6 / (sqrt xₐ * (log 2) ^ 8)
      ≤ (1 : ℝ) / 2000 := by
  rw [hlogxₐ]
  rw [hxₐ, sqrt_exp_3158]
  have htail :
      7 * (3158 : ℝ) ^ 6 / (exp (1579 : ℝ) * (log 2) ^ 8) ≤ (1 : ℝ) / 1000000 := by
    rw [show 7 * (3158 : ℝ) ^ 6 / (exp (1579 : ℝ) * (log 2) ^ 8)
        = 7 * (3158 : ℝ) ^ 6 * exp (-(1579 : ℝ)) / (log 2) ^ 8 by
        field_simp [(show (0 : ℝ) < exp (1579 : ℝ) by positivity).ne']
        rw [show (1 : ℝ) = exp (1579 : ℝ) * exp (-(1579 : ℝ)) by rw [← exp_add]; norm_num]]
    exact tail_small
  linarith [htail, show
    (1 / (3158 : ℝ) + 7 * 2 ^ 8 / (3158 : ℝ) ^ 2 + (1 : ℝ) / 1000000) ≤ (1 : ℝ) / 2000 by
      norm_num]

theorem B_le_small_3157_of
    {xₐ : ℝ}
    (hxₐ : xₐ = exp (3157 : ℝ))
    (hlogxₐ : log xₐ = (3157 : ℝ)) :
    1 / log xₐ + 7 * 2 ^ 8 / log xₐ ^ 2
      + 7 * log xₐ ^ 6 / (sqrt xₐ * (log 2) ^ 8)
      ≤ (1 : ℝ) / 1000 := by
  rw [hlogxₐ]
  rw [hxₐ, sqrt_exp_3157]
  have htail :
      7 * (3157 : ℝ) ^ 6 / (exp ((3157 : ℝ) / 2) * (log 2) ^ 8) ≤ (1 : ℝ) / 1000000 := by
    rw [show 7 * (3157 : ℝ) ^ 6 / (exp ((3157 : ℝ) / 2) * (log 2) ^ 8)
        = 7 * (3157 : ℝ) ^ 6 * exp (-((3157 : ℝ) / 2)) / (log 2) ^ 8 by
        field_simp [(show (0 : ℝ) < exp ((3157 : ℝ) / 2) by positivity).ne']
        rw [show (1 : ℝ) = exp ((3157 : ℝ) / 2) * exp (-((3157 : ℝ) / 2)) by
          rw [← exp_add]
          ring_nf
          simp]]
    exact tail_small_3157
  linarith [htail, show
    (1 / (3157 : ℝ) + 7 * 2 ^ 8 / (3157 : ℝ) ^ 2 + (1 : ℝ) / 1000000) ≤ (1 : ℝ) / 1000 by
      norm_num]

theorem C1_le_one_of
    {a : ℝ → ℝ} {xₐ : ℝ}
    (hxₐ : xₐ = exp (3158 : ℝ))
    (h2xa : 2 ≤ xₐ)
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z)
    (ha_int : IntegrableOn (fun t ↦ a t / log t ^ 7) (Set.Icc 2 xₐ) volume)
    (hJ3120 :
      ∫ t in Set.Icc 2 (exp (3120 : ℝ)), 1 / log t ^ 7
        ≤ exp (3120 : ℝ) / log (exp (3120 : ℝ)) ^ 7
          + 7 * (sqrt (exp (3120 : ℝ)) / log 2 ^ 8
            + 2 ^ 8 * exp (3120 : ℝ) / log (exp (3120 : ℝ)) ^ 8)) :
    log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7 ≤ (1 : ℝ) := by
  have h3120le : exp (3120 : ℝ) ≤ xₐ := by
    rw [hxₐ]
    exact exp_le_exp.mpr (by norm_num)
  let K : ℝ := (100000000000720 : ℝ)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  let f : ℝ → ℝ := fun t ↦ (720 + a t) / log t ^ 7
  have hJ_int : IntegrableOn (fun t : ℝ ↦ 1 / log t ^ 7) (Set.Icc 2 xₐ) volume :=
    ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
      (continuousOn_log.mono <| by
        intro t ht
        exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) (by
      intro t ht
      exact pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1]))
  have hconst_int : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ 7) (Set.Icc 2 xₐ) volume := by
    have htmp : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) * (1 / log t ^ 7)) (Set.Icc 2 xₐ) volume :=
      hJ_int.const_mul 720
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring
  have hadd_int :
      IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ 7 + a t / log t ^ 7) (Set.Icc 2 xₐ) volume :=
    hconst_int.add ha_int
  have hf_int : IntegrableOn f (Set.Icc 2 xₐ) volume := by
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 hadd_int
    intro t ht
    dsimp [f]
    ring
  have hsplit :
      ∫ t in Set.Icc 2 xₐ, f t
        = (∫ t in Set.Icc 2 (exp (3120 : ℝ)), f t)
          + (∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, f t) :=
    integral_Icc_split (f := f) (a := 2) (b := exp (3120 : ℝ)) (c := xₐ)
      (by linarith [add_one_le_exp (3120 : ℝ)]) h3120le hf_int

  have hf_int_low : IntegrableOn f (Set.Icc 2 (exp (3120 : ℝ))) volume :=
    hf_int.mono_set (by intro t ht; exact ⟨ht.1, le_trans ht.2 h3120le⟩)
  have hlow_rhs_int :
      IntegrableOn (fun t : ℝ ↦ K / log t ^ 7) (Set.Icc 2 (exp (3120 : ℝ))) volume := by
    have htmp :
        IntegrableOn (fun t : ℝ ↦ K * (1 / log t ^ 7)) (Set.Icc 2 (exp (3120 : ℝ))) volume :=
      (ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
        (continuousOn_log.mono <| by
          intro t ht
          exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) (by
        intro t ht
        exact pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1]))).const_mul K
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring
  have hlow_pt : ∀ t ∈ Set.Icc 2 (exp (3120 : ℝ)), f t ≤ K / log t ^ 7 := by
    intro t ht
    have ha_le : a t ≤ (100000000000000 : ℝ) := a_low_huge_of ha_eq_admissible_ge_two ht
    have hnum_le : 720 + a t ≤ K := by
      dsimp [K]
      linarith
    have hlog_nonneg : 0 ≤ log t := log_nonneg (by linarith [ht.1])
    dsimp [f]
    exact div_le_div_of_nonneg_right hnum_le (pow_nonneg hlog_nonneg 7)
  have hlow_le_rhs :
      ∫ t in Set.Icc 2 (exp (3120 : ℝ)), f t
        ≤ ∫ t in Set.Icc 2 (exp (3120 : ℝ)), K / log t ^ 7 :=
    MeasureTheory.setIntegral_mono_on hf_int_low hlow_rhs_int measurableSet_Icc hlow_pt
  have hlow_factor :
      ∫ t in Set.Icc 2 (exp (3120 : ℝ)), K / log t ^ 7
        = K * ∫ t in Set.Icc 2 (exp (3120 : ℝ)), 1 / log t ^ 7 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    ring
  have hlow_le :
      ∫ t in Set.Icc 2 (exp (3120 : ℝ)), f t
        ≤ K * (exp (3120 : ℝ) / log (exp (3120 : ℝ)) ^ 7
          + 7 * (sqrt (exp (3120 : ℝ)) / log 2 ^ 8
            + 2 ^ 8 * exp (3120 : ℝ) / log (exp (3120 : ℝ)) ^ 8)) := by
    rw [hlow_factor] at hlow_le_rhs
    exact le_trans hlow_le_rhs (mul_le_mul_of_nonneg_left hJ3120 hK_nonneg)

  have hf_int_high : IntegrableOn f (Set.Icc (exp (3120 : ℝ)) xₐ) volume :=
    hf_int.mono_set (by intro t ht; exact ⟨le_trans (by linarith [add_one_le_exp (3120 : ℝ)]) ht.1, ht.2⟩)
  have hconst_high_int :
      IntegrableOn (fun _ : ℝ ↦ (2020 : ℝ) / (3120 : ℝ) ^ 7) (Set.Icc (exp (3120 : ℝ)) xₐ) volume :=
    ContinuousOn.integrableOn_Icc continuousOn_const
  have ha_mono_3120 : AntitoneOn a (Set.Ici (exp (3120 : ℝ))) := by
    intro x hx y hy hxy
    exact (a_mono_of ha_eq_admissible_ge_two)
      (Set.mem_Ici.mpr <| le_trans (exp_le_exp.mpr (by norm_num : (236 : ℝ) ≤ 3120)) hx)
      (Set.mem_Ici.mpr <| le_trans (exp_le_exp.mpr (by norm_num : (236 : ℝ) ≤ 3120)) hy)
      hxy
  have ha_3120_upper : a (exp (3120 : ℝ)) ≤ (1300 : ℝ) := a_3120_upper_of ha_eq_admissible_ge_two
  have hhigh_pt : ∀ t ∈ Set.Icc (exp (3120 : ℝ)) xₐ, f t ≤ (2020 : ℝ) / (3120 : ℝ) ^ 7 := by
    intro t ht
    have hat3120 : a t ≤ a (exp (3120 : ℝ)) :=
      ha_mono_3120
        (Set.mem_Ici.mpr (le_rfl : exp (3120 : ℝ) ≤ exp (3120 : ℝ)))
        (Set.mem_Ici.mpr ht.1) ht.1
    have hat : a t ≤ 1300 := le_trans hat3120 ha_3120_upper
    have hnum_le : 720 + a t ≤ 2020 := by linarith
    have hlog_ge : (3120 : ℝ) ≤ log t := by
      have h := log_le_log (by positivity : (0 : ℝ) < exp (3120 : ℝ)) ht.1
      simpa [log_exp] using h
    have hpow : (3120 : ℝ) ^ 7 ≤ log t ^ 7 := pow_le_pow_left₀ (by norm_num) hlog_ge 7
    have hlog_nonneg : 0 ≤ log t := by linarith [hlog_ge]
    calc
      f t = (720 + a t) / log t ^ 7 := rfl
      _ ≤ (2020 : ℝ) / log t ^ 7 := by
        exact div_le_div_of_nonneg_right hnum_le (pow_nonneg hlog_nonneg 7)
      _ ≤ (2020 : ℝ) / (3120 : ℝ) ^ 7 := by
        exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (2020 : ℝ)) (by positivity) hpow
  have hhigh_le_const :
      ∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, f t
        ≤ ∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, (2020 : ℝ) / (3120 : ℝ) ^ 7 :=
    MeasureTheory.setIntegral_mono_on hf_int_high hconst_high_int measurableSet_Icc hhigh_pt
  have hhigh_const_eval :
      ∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, (2020 : ℝ) / (3120 : ℝ) ^ 7
        = (2020 : ℝ) / (3120 : ℝ) ^ 7 * (xₐ - exp (3120 : ℝ)) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h3120le,
      intervalIntegral.integral_const]
    simp [smul_eq_mul, mul_comm]
  have hhigh_le :
      ∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, f t
        ≤ (2020 : ℝ) / (3120 : ℝ) ^ 7 * xₐ := by
    have hstep :
        (2020 : ℝ) / (3120 : ℝ) ^ 7 * (xₐ - exp (3120 : ℝ))
          ≤ (2020 : ℝ) / (3120 : ℝ) ^ 7 * xₐ := by
      exact mul_le_mul_of_nonneg_left
        (by linarith [show (0 : ℝ) ≤ exp (3120 : ℝ) by positivity]) (by positivity)
    calc
      ∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, f t
        ≤ (2020 : ℝ) / (3120 : ℝ) ^ 7 * (xₐ - exp (3120 : ℝ)) := by
            simpa [hhigh_const_eval] using hhigh_le_const
      _ ≤ (2020 : ℝ) / (3120 : ℝ) ^ 7 * xₐ := hstep

  have hmain :
      log xₐ ^ 6 / xₐ *
          ((∫ t in Set.Icc 2 (exp (3120 : ℝ)), f t) + (∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, f t))
        ≤ log xₐ ^ 6 / xₐ *
            (K * (exp (3120 : ℝ) / log (exp (3120 : ℝ)) ^ 7
              + 7 * (sqrt (exp (3120 : ℝ)) / log 2 ^ 8
                + 2 ^ 8 * exp (3120 : ℝ) / log (exp (3120 : ℝ)) ^ 8))
              + (2020 : ℝ) / (3120 : ℝ) ^ 7 * xₐ) :=
    mul_le_mul_of_nonneg_left (by linarith [hlow_le, hhigh_le]) (by positivity)
  have hmain' :
      (3158 : ℝ) ^ 6 / exp (3158 : ℝ) *
          ((∫ t in Set.Icc 2 (exp (3120 : ℝ)), f t)
            + (∫ t in Set.Icc (exp (3120 : ℝ)) (exp (3158 : ℝ)), f t))
        ≤ (3158 : ℝ) ^ 6 / exp (3158 : ℝ) *
          (K * (exp (3120 : ℝ) / (3120 : ℝ) ^ 7
            + 7 * (sqrt (exp (3120 : ℝ)) / log 2 ^ 8
              + 2 ^ 8 * exp (3120 : ℝ) / (3120 : ℝ) ^ 8))
            + (2020 : ℝ) / (3120 : ℝ) ^ 7 * exp (3158 : ℝ)) := by
    simpa [hxₐ, log_exp] using hmain
  have hdecomp :
      (3158 : ℝ) ^ 6 / exp (3158 : ℝ) *
          (K * (exp (3120 : ℝ) / (3120 : ℝ) ^ 7
            + 7 * (sqrt (exp (3120 : ℝ)) / log 2 ^ 8
              + 2 ^ 8 * exp (3120 : ℝ) / (3120 : ℝ) ^ 8))
            + (2020 : ℝ) / (3120 : ℝ) ^ 7 * exp (3158 : ℝ))
        = (3158 : ℝ) ^ 6 / exp (3158 : ℝ) *
            (K * (exp (3120 : ℝ) / (3120 : ℝ) ^ 7
              + 7 * (sqrt (exp (3120 : ℝ)) / log 2 ^ 8
                + 2 ^ 8 * exp (3120 : ℝ) / (3120 : ℝ) ^ 8)))
          + (2020 : ℝ) * (3158 : ℝ) ^ 6 / (3120 : ℝ) ^ 7 := by
    field_simp
  rw [hdecomp] at hmain'
  dsimp [K] at hmain'
  have hfin :
      (3158 : ℝ) ^ 6 / exp (3158 : ℝ) *
          ((100000000000720 : ℝ) *
            (exp (3120 : ℝ) / (3120 : ℝ) ^ 7
              + 7 *
                (sqrt (exp (3120 : ℝ)) / (log 2) ^ 8
                  + (2 : ℝ) ^ 8 * exp (3120 : ℝ) / (3120 : ℝ) ^ 8)))
          + (2020 : ℝ) * (3158 : ℝ) ^ 6 / (3120 : ℝ) ^ 7 ≤ 1 := by
    nlinarith [low_contrib_raw_le_one_tenth, high_contrib_le_seven_tenths]
  exact le_trans (by rw [hsplit]; simpa [f, hxₐ, log_exp] using hmain') hfin

theorem C1_le_one_3157_of
    {a : ℝ → ℝ} {xₐ : ℝ}
    (hxₐ : xₐ = exp (3157 : ℝ))
    (h2xa : 2 ≤ xₐ)
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z)
    (ha_int : IntegrableOn (fun t ↦ a t / log t ^ 7) (Set.Icc 2 xₐ) volume)
    (hJ3120 :
      ∫ t in Set.Icc 2 (exp (3120 : ℝ)), 1 / log t ^ 7
        ≤ exp (3120 : ℝ) / log (exp (3120 : ℝ)) ^ 7
          + 7 * (sqrt (exp (3120 : ℝ)) / log 2 ^ 8
            + 2 ^ 8 * exp (3120 : ℝ) / log (exp (3120 : ℝ)) ^ 8)) :
    log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7 ≤ (1 : ℝ) := by
  have h3120le : exp (3120 : ℝ) ≤ xₐ := by
    rw [hxₐ]
    exact exp_le_exp.mpr (by norm_num)
  let K : ℝ := (100000000000720 : ℝ)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  let f : ℝ → ℝ := fun t ↦ (720 + a t) / log t ^ 7
  have hJ_int : IntegrableOn (fun t : ℝ ↦ 1 / log t ^ 7) (Set.Icc 2 xₐ) volume :=
    ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
      (continuousOn_log.mono <| by
        intro t ht
        exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) (by
      intro t ht
      exact pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1]))
  have hconst_int : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ 7) (Set.Icc 2 xₐ) volume := by
    have htmp : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) * (1 / log t ^ 7)) (Set.Icc 2 xₐ) volume :=
      hJ_int.const_mul 720
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring
  have hadd_int :
      IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ 7 + a t / log t ^ 7) (Set.Icc 2 xₐ) volume :=
    hconst_int.add ha_int
  have hf_int : IntegrableOn f (Set.Icc 2 xₐ) volume := by
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 hadd_int
    intro t ht
    dsimp [f]
    ring
  have hsplit :
      ∫ t in Set.Icc 2 xₐ, f t
        = (∫ t in Set.Icc 2 (exp (3120 : ℝ)), f t)
          + (∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, f t) :=
    integral_Icc_split (f := f) (a := 2) (b := exp (3120 : ℝ)) (c := xₐ)
      (by linarith [add_one_le_exp (3120 : ℝ)]) h3120le hf_int

  have hf_int_low : IntegrableOn f (Set.Icc 2 (exp (3120 : ℝ))) volume :=
    hf_int.mono_set (by intro t ht; exact ⟨ht.1, le_trans ht.2 h3120le⟩)
  have hlow_rhs_int :
      IntegrableOn (fun t : ℝ ↦ K / log t ^ 7) (Set.Icc 2 (exp (3120 : ℝ))) volume := by
    have htmp :
        IntegrableOn (fun t : ℝ ↦ K * (1 / log t ^ 7)) (Set.Icc 2 (exp (3120 : ℝ))) volume :=
      (ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
        (continuousOn_log.mono <| by
          intro t ht
          exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) (by
        intro t ht
        exact pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1]))).const_mul K
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring
  have hlow_pt : ∀ t ∈ Set.Icc 2 (exp (3120 : ℝ)), f t ≤ K / log t ^ 7 := by
    intro t ht
    have ha_le : a t ≤ (100000000000000 : ℝ) := a_low_huge_of ha_eq_admissible_ge_two ht
    have hnum_le : 720 + a t ≤ K := by
      dsimp [K]
      linarith
    have hlog_nonneg : 0 ≤ log t := log_nonneg (by linarith [ht.1])
    dsimp [f]
    exact div_le_div_of_nonneg_right hnum_le (pow_nonneg hlog_nonneg 7)
  have hlow_le_rhs :
      ∫ t in Set.Icc 2 (exp (3120 : ℝ)), f t
        ≤ ∫ t in Set.Icc 2 (exp (3120 : ℝ)), K / log t ^ 7 :=
    MeasureTheory.setIntegral_mono_on hf_int_low hlow_rhs_int measurableSet_Icc hlow_pt
  have hlow_factor :
      ∫ t in Set.Icc 2 (exp (3120 : ℝ)), K / log t ^ 7
        = K * ∫ t in Set.Icc 2 (exp (3120 : ℝ)), 1 / log t ^ 7 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    ring
  have hlow_le :
      ∫ t in Set.Icc 2 (exp (3120 : ℝ)), f t
        ≤ K * (exp (3120 : ℝ) / log (exp (3120 : ℝ)) ^ 7
          + 7 * (sqrt (exp (3120 : ℝ)) / log 2 ^ 8
            + 2 ^ 8 * exp (3120 : ℝ) / log (exp (3120 : ℝ)) ^ 8)) := by
    rw [hlow_factor] at hlow_le_rhs
    exact le_trans hlow_le_rhs (mul_le_mul_of_nonneg_left hJ3120 hK_nonneg)

  have hf_int_high : IntegrableOn f (Set.Icc (exp (3120 : ℝ)) xₐ) volume :=
    hf_int.mono_set (by intro t ht; exact ⟨le_trans (by linarith [add_one_le_exp (3120 : ℝ)]) ht.1, ht.2⟩)
  have hconst_high_int :
      IntegrableOn (fun _ : ℝ ↦ (2020 : ℝ) / (3120 : ℝ) ^ 7) (Set.Icc (exp (3120 : ℝ)) xₐ) volume :=
    ContinuousOn.integrableOn_Icc continuousOn_const
  have ha_mono_3120 : AntitoneOn a (Set.Ici (exp (3120 : ℝ))) := by
    intro x hx y hy hxy
    exact (a_mono_of ha_eq_admissible_ge_two)
      (Set.mem_Ici.mpr <| le_trans (exp_le_exp.mpr (by norm_num : (236 : ℝ) ≤ 3120)) hx)
      (Set.mem_Ici.mpr <| le_trans (exp_le_exp.mpr (by norm_num : (236 : ℝ) ≤ 3120)) hy)
      hxy
  have ha_3120_upper : a (exp (3120 : ℝ)) ≤ (1300 : ℝ) := a_3120_upper_of ha_eq_admissible_ge_two
  have hhigh_pt : ∀ t ∈ Set.Icc (exp (3120 : ℝ)) xₐ, f t ≤ (2020 : ℝ) / (3120 : ℝ) ^ 7 := by
    intro t ht
    have hat3120 : a t ≤ a (exp (3120 : ℝ)) :=
      ha_mono_3120
        (Set.mem_Ici.mpr (le_rfl : exp (3120 : ℝ) ≤ exp (3120 : ℝ)))
        (Set.mem_Ici.mpr ht.1) ht.1
    have hat : a t ≤ 1300 := le_trans hat3120 ha_3120_upper
    have hnum_le : 720 + a t ≤ 2020 := by linarith
    have hlog_ge : (3120 : ℝ) ≤ log t := by
      have h := log_le_log (by positivity : (0 : ℝ) < exp (3120 : ℝ)) ht.1
      simpa [log_exp] using h
    have hpow : (3120 : ℝ) ^ 7 ≤ log t ^ 7 := pow_le_pow_left₀ (by norm_num) hlog_ge 7
    have hlog_nonneg : 0 ≤ log t := by linarith [hlog_ge]
    calc
      f t = (720 + a t) / log t ^ 7 := rfl
      _ ≤ (2020 : ℝ) / log t ^ 7 := by
        exact div_le_div_of_nonneg_right hnum_le (pow_nonneg hlog_nonneg 7)
      _ ≤ (2020 : ℝ) / (3120 : ℝ) ^ 7 := by
        exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (2020 : ℝ)) (by positivity) hpow
  have hhigh_le_const :
      ∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, f t
        ≤ ∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, (2020 : ℝ) / (3120 : ℝ) ^ 7 :=
    MeasureTheory.setIntegral_mono_on hf_int_high hconst_high_int measurableSet_Icc hhigh_pt
  have hhigh_const_eval :
      ∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, (2020 : ℝ) / (3120 : ℝ) ^ 7
        = (2020 : ℝ) / (3120 : ℝ) ^ 7 * (xₐ - exp (3120 : ℝ)) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h3120le,
      intervalIntegral.integral_const]
    simp [smul_eq_mul, mul_comm]
  have hhigh_le :
      ∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, f t
        ≤ (2020 : ℝ) / (3120 : ℝ) ^ 7 * xₐ := by
    have hstep :
        (2020 : ℝ) / (3120 : ℝ) ^ 7 * (xₐ - exp (3120 : ℝ))
          ≤ (2020 : ℝ) / (3120 : ℝ) ^ 7 * xₐ := by
      exact mul_le_mul_of_nonneg_left
        (by linarith [show (0 : ℝ) ≤ exp (3120 : ℝ) by positivity]) (by positivity)
    calc
      ∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, f t
        ≤ (2020 : ℝ) / (3120 : ℝ) ^ 7 * (xₐ - exp (3120 : ℝ)) := by
            simpa [hhigh_const_eval] using hhigh_le_const
      _ ≤ (2020 : ℝ) / (3120 : ℝ) ^ 7 * xₐ := hstep

  have hmain :
      log xₐ ^ 6 / xₐ *
          ((∫ t in Set.Icc 2 (exp (3120 : ℝ)), f t) + (∫ t in Set.Icc (exp (3120 : ℝ)) xₐ, f t))
        ≤ log xₐ ^ 6 / xₐ *
            (K * (exp (3120 : ℝ) / log (exp (3120 : ℝ)) ^ 7
              + 7 * (sqrt (exp (3120 : ℝ)) / log 2 ^ 8
                + 2 ^ 8 * exp (3120 : ℝ) / log (exp (3120 : ℝ)) ^ 8))
              + (2020 : ℝ) / (3120 : ℝ) ^ 7 * xₐ) :=
    mul_le_mul_of_nonneg_left (by linarith [hlow_le, hhigh_le]) (by positivity)
  have hmain' :
      (3157 : ℝ) ^ 6 / exp (3157 : ℝ) *
          ((∫ t in Set.Icc 2 (exp (3120 : ℝ)), f t)
            + (∫ t in Set.Icc (exp (3120 : ℝ)) (exp (3157 : ℝ)), f t))
        ≤ (3157 : ℝ) ^ 6 / exp (3157 : ℝ) *
          (K * (exp (3120 : ℝ) / (3120 : ℝ) ^ 7
            + 7 * (sqrt (exp (3120 : ℝ)) / log 2 ^ 8
              + 2 ^ 8 * exp (3120 : ℝ) / (3120 : ℝ) ^ 8))
            + (2020 : ℝ) / (3120 : ℝ) ^ 7 * exp (3157 : ℝ)) := by
    simpa [hxₐ, log_exp] using hmain
  have hdecomp :
      (3157 : ℝ) ^ 6 / exp (3157 : ℝ) *
          (K * (exp (3120 : ℝ) / (3120 : ℝ) ^ 7
            + 7 * (sqrt (exp (3120 : ℝ)) / log 2 ^ 8
              + 2 ^ 8 * exp (3120 : ℝ) / (3120 : ℝ) ^ 8))
            + (2020 : ℝ) / (3120 : ℝ) ^ 7 * exp (3157 : ℝ))
        = (3157 : ℝ) ^ 6 / exp (3157 : ℝ) *
            (K * (exp (3120 : ℝ) / (3120 : ℝ) ^ 7
              + 7 * (sqrt (exp (3120 : ℝ)) / log 2 ^ 8
                + 2 ^ 8 * exp (3120 : ℝ) / (3120 : ℝ) ^ 8)))
          + (2020 : ℝ) * (3157 : ℝ) ^ 6 / (3120 : ℝ) ^ 7 := by
    field_simp
  rw [hdecomp] at hmain'
  dsimp [K] at hmain'
  have hfin :
      (3157 : ℝ) ^ 6 / exp (3157 : ℝ) *
          ((100000000000720 : ℝ) *
            (exp (3120 : ℝ) / (3120 : ℝ) ^ 7
              + 7 *
                (sqrt (exp (3120 : ℝ)) / (log 2) ^ 8
                  + (2 : ℝ) ^ 8 * exp (3120 : ℝ) / (3120 : ℝ) ^ 8)))
          + (2020 : ℝ) * (3157 : ℝ) ^ 6 / (3120 : ℝ) ^ 7 ≤ 1 := by
    nlinarith [low_contrib_raw_le_one_tenth_3157, high_contrib_le_seven_tenths_3157]
  exact le_trans (by rw [hsplit]; simpa [f, hxₐ, log_exp] using hmain') hfin

theorem M_upper_from_bounds
    {a_xa a_exa C1 B : ℝ}
    (hax0 : 0 ≤ a_xa) (hC1 : C1 ≤ (1 : ℝ))
    (hax : a_xa ≤ (1054 : ℝ)) (haex : a_exa ≤ (1048 : ℝ))
    (hB : B ≤ (1 : ℝ) / 2000) :
    120 + a_exa + C1 + (720 + a_xa) * B ≤ (1170 : ℝ) := by
  have : (720 + a_xa) * B ≤ (1774 : ℝ) * ((1 : ℝ) / 2000) :=
    le_trans (mul_le_mul_of_nonneg_left hB (by linarith))
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  nlinarith [hC1, haex]

theorem sqrt_exp_2272 : sqrt (exp (2272 : ℝ)) = exp (1136 : ℝ) := by
  rw [show (2272 : ℝ) = 1136 + 1136 by norm_num, exp_add, sqrt_mul (by positivity)]
  nlinarith [Real.sq_sqrt (show 0 ≤ exp (1136 : ℝ) by positivity)]

theorem tail_small_2272 :
    7 * (2272 : ℝ) ^ 6 * exp (-(1136 : ℝ)) / (log 2) ^ 8 ≤ (1e-10 : ℝ) := by
  have h := (show ∀ y ∈ Set.Icc (2272 : ℝ) 2272,
      7 * y ^ 6 * exp (-(y / 2)) / (log 2) ^ 8 ≤ (1e-10 : ℝ) by
    interval_bound 20) 2272 ⟨le_rfl, le_rfl⟩
  simpa [show (2272 : ℝ) / 2 = (1136 : ℝ) by norm_num] using h

theorem B_le_one_2272_of
    {xₐ : ℝ}
    (hxₐ : xₐ = exp (2272 : ℝ))
    (hlogxₐ : log xₐ = (2272 : ℝ)) :
    1 / log xₐ + 7 * 2 ^ (8 : ℕ) / log xₐ ^ (2 : ℕ)
      + 7 * log xₐ ^ (6 : ℕ) / (sqrt xₐ * log 2 ^ (8 : ℕ)) ≤ (1 : ℝ) := by
  rw [hlogxₐ, hxₐ, sqrt_exp_2272]
  have hthird :
      7 * (2272 : ℝ) ^ (6 : ℕ) / (exp (1136 : ℝ) * log 2 ^ (8 : ℕ)) ≤ (1e-10 : ℝ) := by
    have hExpinv : (1 : ℝ) / exp (1136 : ℝ) = exp (-(1136 : ℝ)) := by
      rw [one_div, ← Real.exp_neg]
    calc
      7 * (2272 : ℝ) ^ (6 : ℕ) / (exp (1136 : ℝ) * log 2 ^ (8 : ℕ))
          = 7 * (2272 : ℝ) ^ (6 : ℕ) * exp (-(1136 : ℝ)) / (log 2) ^ (8 : ℕ) := by
              rw [show 7 * (2272 : ℝ) ^ (6 : ℕ) / (exp (1136 : ℝ) * log 2 ^ (8 : ℕ))
                  = 7 * (2272 : ℝ) ^ (6 : ℕ) * ((1 : ℝ) / exp (1136 : ℝ)) / (log 2) ^ (8 : ℕ) by
                  field_simp [(show (0 : ℝ) < exp (1136 : ℝ) by positivity).ne']]
              rw [hExpinv]
      _ ≤ (1e-10 : ℝ) := tail_small_2272
  have hmain :
      (1 / (2272 : ℝ) + 7 * 2 ^ (8 : ℕ) / (2272 : ℝ) ^ (2 : ℕ) + (1e-10 : ℝ)) ≤ (1 : ℝ) := by
    norm_num
  nlinarith

theorem C1_le_big_2272_of
    {a : ℝ → ℝ} {xₐ : ℝ}
    (hxₐ : xₐ = exp (2272 : ℝ))
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z)
    (ha_int : IntegrableOn (fun t ↦ a t / log t ^ 7) (Set.Icc 2 xₐ) volume)
    (hJ2272 :
      ∫ t in Set.Icc 2 (exp (2272 : ℝ)), 1 / log t ^ 7
        ≤ exp (2272 : ℝ) / log (exp (2272 : ℝ)) ^ 7
          + 7 * (sqrt (exp (2272 : ℝ)) / log 2 ^ 8
            + 2 ^ 8 * exp (2272 : ℝ) / log (exp (2272 : ℝ)) ^ 8)) :
    log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7 ≤ (78729500000 : ℝ) := by
  let K : ℝ := (100000000000720 : ℝ)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  let f : ℝ → ℝ := fun t ↦ (720 + a t) / log t ^ 7
  have hJ_int : IntegrableOn (fun t : ℝ ↦ 1 / log t ^ 7) (Set.Icc 2 xₐ) volume :=
    ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
      (continuousOn_log.mono <| by
        intro t ht
        exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) (by
      intro t ht
      exact pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1]))
  have hconst_int : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ 7) (Set.Icc 2 xₐ) volume := by
    have htmp : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) * (1 / log t ^ 7)) (Set.Icc 2 xₐ) volume :=
      hJ_int.const_mul 720
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring
  have hadd_int :
      IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ 7 + a t / log t ^ 7) (Set.Icc 2 xₐ) volume :=
    hconst_int.add ha_int
  have hf_int : IntegrableOn f (Set.Icc 2 xₐ) volume := by
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 hadd_int
    intro t ht
    dsimp [f]
    ring
  have hlow_rhs_int :
      IntegrableOn (fun t : ℝ ↦ K / log t ^ 7) (Set.Icc 2 xₐ) volume := by
    have htmp :
        IntegrableOn (fun t : ℝ ↦ K * (1 / log t ^ 7)) (Set.Icc 2 xₐ) volume :=
      hJ_int.const_mul K
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring
  have hlow_pt : ∀ t ∈ Set.Icc 2 xₐ, f t ≤ K / log t ^ 7 := by
    intro t ht
    have ht3120 : t ∈ Set.Icc 2 (exp (3120 : ℝ)) := by
      constructor
      · exact ht.1
      · rw [hxₐ] at ht
        exact le_trans ht.2 (exp_le_exp.mpr (by norm_num))
    have ha_le : a t ≤ (100000000000000 : ℝ) := a_low_huge_of ha_eq_admissible_ge_two ht3120
    have hnum_le : 720 + a t ≤ K := by
      dsimp [K]
      linarith
    have hlog_nonneg : 0 ≤ log t := log_nonneg (by linarith [ht.1])
    dsimp [f]
    exact div_le_div_of_nonneg_right hnum_le (pow_nonneg hlog_nonneg 7)
  have hlow_le_rhs :
      ∫ t in Set.Icc 2 xₐ, f t ≤ ∫ t in Set.Icc 2 xₐ, K / log t ^ 7 :=
    MeasureTheory.setIntegral_mono_on hf_int hlow_rhs_int measurableSet_Icc hlow_pt
  have hlow_factor :
      ∫ t in Set.Icc 2 xₐ, K / log t ^ 7 = K * ∫ t in Set.Icc 2 xₐ, 1 / log t ^ 7 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    ring
  have hlow_le :
      ∫ t in Set.Icc 2 xₐ, f t
        ≤ K * (exp (2272 : ℝ) / log (exp (2272 : ℝ)) ^ 7
          + 7 * (sqrt (exp (2272 : ℝ)) / log 2 ^ 8
            + 2 ^ 8 * exp (2272 : ℝ) / log (exp (2272 : ℝ)) ^ 8)) := by
    have hlow_le_rhs' :
        ∫ t in Set.Icc 2 xₐ, f t
          ≤ K * ∫ t in Set.Icc 2 (exp (2272 : ℝ)), 1 / log t ^ 7 := by
      rw [hlow_factor] at hlow_le_rhs
      simpa [hxₐ] using hlow_le_rhs
    exact le_trans hlow_le_rhs' (mul_le_mul_of_nonneg_left hJ2272 hK_nonneg)
  have hmain :
      (2272 : ℝ) ^ 6 / exp (2272 : ℝ) *
          (K * (exp (2272 : ℝ) / (2272 : ℝ) ^ 7
            + 7 * (sqrt (exp (2272 : ℝ)) / log 2 ^ 8
              + 2 ^ 8 * exp (2272 : ℝ) / (2272 : ℝ) ^ 8))) ≤ (78729500000 : ℝ) := by
    rw [sqrt_exp_2272]
    have hExpSplit : exp (2272 : ℝ) = exp (1136 : ℝ) * exp (1136 : ℝ) := by
      rw [show (2272 : ℝ) = (1136 : ℝ) + 1136 by norm_num, exp_add]
    have hthird :
        7 * (2272 : ℝ) ^ 6 / (exp (1136 : ℝ) * log 2 ^ 8) ≤ (1e-10 : ℝ) := by
      have hExpinv : (1 : ℝ) / exp (1136 : ℝ) = exp (-(1136 : ℝ)) := by
        rw [one_div, ← Real.exp_neg]
      calc
        7 * (2272 : ℝ) ^ 6 / (exp (1136 : ℝ) * log 2 ^ 8)
            = 7 * (2272 : ℝ) ^ 6 * exp (-(1136 : ℝ)) / (log 2) ^ 8 := by
                rw [show 7 * (2272 : ℝ) ^ 6 / (exp (1136 : ℝ) * log 2 ^ 8)
                    = 7 * (2272 : ℝ) ^ 6 * ((1 : ℝ) / exp (1136 : ℝ)) / (log 2) ^ 8 by
                    field_simp [(show (0 : ℝ) < exp (1136 : ℝ) by positivity).ne']]
                rw [hExpinv]
        _ ≤ (1e-10 : ℝ) := tail_small_2272
    have hrewrite :
        (2272 : ℝ) ^ 6 / exp (2272 : ℝ) *
            (K * (exp (2272 : ℝ) / (2272 : ℝ) ^ 7
              + 7 * (exp (1136 : ℝ) / log 2 ^ 8
                + 2 ^ 8 * exp (2272 : ℝ) / (2272 : ℝ) ^ 8)))
          = K * ((1 : ℝ) / (2272 : ℝ)
              + 7 * (2272 : ℝ) ^ 6 / (exp (1136 : ℝ) * log 2 ^ 8)
              + 7 * 2 ^ 8 / (2272 : ℝ) ^ 2) := by
      rw [hExpSplit]
      field_simp [K]
      ring
    rw [hrewrite]
    have hbracket :
        (1 : ℝ) / (2272 : ℝ)
          + 7 * (2272 : ℝ) ^ 6 / (exp (1136 : ℝ) * log 2 ^ 8)
          + 7 * 2 ^ 8 / (2272 : ℝ) ^ 2
        ≤ (1 : ℝ) / (2272 : ℝ) + (1e-10 : ℝ) + 7 * 2 ^ 8 / (2272 : ℝ) ^ 2 := by
      nlinarith
    have hfinal :
        K * ((1 : ℝ) / (2272 : ℝ) + (1e-10 : ℝ) + 7 * 2 ^ 8 / (2272 : ℝ) ^ 2)
          ≤ (78729500000 : ℝ) := by
      norm_num [K]
    exact le_trans (mul_le_mul_of_nonneg_left hbracket hK_nonneg) hfinal
  rw [hxₐ, log_exp]
  have hscale_nonneg : 0 ≤ (2272 : ℝ) ^ 6 / exp (2272 : ℝ) := by
    positivity
  have hlow_le' :
      ∫ t in Set.Icc 2 (exp (2272 : ℝ)), f t
        ≤ K * (exp (2272 : ℝ) / (2272 : ℝ) ^ 7
          + 7 * (sqrt (exp (2272 : ℝ)) / log 2 ^ 8
            + 2 ^ 8 * exp (2272 : ℝ) / (2272 : ℝ) ^ 8)) := by
    have hlow_le'' := hlow_le
    simpa [hxₐ, log_exp] using hlow_le''
  exact le_trans
    (mul_le_mul_of_nonneg_left hlow_le' hscale_nonneg)
    hmain

theorem sqrt_exp_770 : sqrt (exp (770 : ℝ)) = exp (385 : ℝ) := by
  rw [show (770 : ℝ) = 385 + 385 by norm_num, exp_add, sqrt_mul (by positivity)]
  nlinarith [Real.sq_sqrt (show 0 ≤ exp (385 : ℝ) by positivity)]

theorem sqrt_exp_792 : sqrt (exp (792 : ℝ)) = exp (396 : ℝ) := by
  rw [show (792 : ℝ) = 396 + 396 by norm_num, exp_add, sqrt_mul (by positivity)]
  nlinarith [Real.sq_sqrt (show 0 ≤ exp (396 : ℝ) by positivity)]

theorem tail_small_792 :
    7 * (792 : ℝ) ^ 6 * exp (-(396 : ℝ)) / (log 2) ^ 8 ≤ (1e-10 : ℝ) := by
  have h := (show ∀ y ∈ Set.Icc (792 : ℝ) 792,
      7 * y ^ 6 * exp (-(y / 2)) / (log 2) ^ 8 ≤ (1e-10 : ℝ) by
    interval_bound 20) 792 ⟨le_rfl, le_rfl⟩
  simpa [show (792 : ℝ) / 2 = (396 : ℝ) by norm_num] using h

theorem B_le_small_792_of
    {xₐ : ℝ}
    (hxₐ : xₐ = exp (792 : ℝ))
    (hlogxₐ : log xₐ = (792 : ℝ)) :
    1 / log xₐ + 7 * 2 ^ (8 : ℕ) / log xₐ ^ (2 : ℕ)
      + 7 * log xₐ ^ (6 : ℕ) / (sqrt xₐ * log 2 ^ (8 : ℕ)) ≤ (103 / 25000 : ℝ) := by
  rw [hlogxₐ, hxₐ, sqrt_exp_792]
  have hthird :
      7 * (792 : ℝ) ^ (6 : ℕ) / (exp (396 : ℝ) * log 2 ^ (8 : ℕ)) ≤ (1e-10 : ℝ) := by
    have hExpinv : (1 : ℝ) / exp (396 : ℝ) = exp (-(396 : ℝ)) := by
      rw [one_div, ← Real.exp_neg]
    calc
      7 * (792 : ℝ) ^ (6 : ℕ) / (exp (396 : ℝ) * log 2 ^ (8 : ℕ))
          = 7 * (792 : ℝ) ^ (6 : ℕ) * exp (-(396 : ℝ)) / (log 2) ^ (8 : ℕ) := by
              rw [show 7 * (792 : ℝ) ^ (6 : ℕ) / (exp (396 : ℝ) * log 2 ^ (8 : ℕ))
                  = 7 * (792 : ℝ) ^ (6 : ℕ) * ((1 : ℝ) / exp (396 : ℝ)) / (log 2) ^ (8 : ℕ) by
                  field_simp [(show (0 : ℝ) < exp (396 : ℝ) by positivity).ne']]
              rw [hExpinv]
      _ ≤ (1e-10 : ℝ) := tail_small_792
  have hmain :
      (1 / (792 : ℝ) + 7 * 2 ^ (8 : ℕ) / (792 : ℝ) ^ (2 : ℕ) + (1e-10 : ℝ)) ≤ (103 / 25000 : ℝ) := by
    norm_num
  nlinarith

theorem low_contrib_raw_le_two_hundred_792_770 :
    (792 : ℝ) ^ 6 * (100000000000720 : ℝ) *
      (exp (-(22 : ℝ)) / (770 : ℝ) ^ 7
        + 7 * (exp (-(407 : ℝ)) / (log 2) ^ 8
          + (2 : ℝ) ^ 8 * exp (-(22 : ℝ)) / (770 : ℝ) ^ 8))
      ≤ (200 : ℝ) := by
  have exp_neg22_small : exp (-(22 : ℝ)) ≤ (3e-10 : ℝ) := by
    have haux : ∀ y ∈ Set.Icc (-22 : ℝ) (-22 : ℝ), exp y ≤ (3e-10 : ℝ) := by
      interval_bound 20
    simpa using haux (-22 : ℝ) ⟨le_rfl, le_rfl⟩
  have exp_neg407_small : exp (-(407 : ℝ)) ≤ (1e-170 : ℝ) := by
    have haux : ∀ y ∈ Set.Icc (-407 : ℝ) (-407 : ℝ), exp y ≤ (1e-170 : ℝ) := by
      interval_bound 20
    simpa using haux (-407 : ℝ) ⟨le_rfl, le_rfl⟩
  have hAcoeff :
      (792 : ℝ) ^ 6 * (100000000000720 : ℝ) / (770 : ℝ) ^ 7 ≤ (154000000000 : ℝ) := by
    norm_num
  have hA :
      (792 : ℝ) ^ 6 * (100000000000720 : ℝ) * exp (-(22 : ℝ)) / (770 : ℝ) ^ 7 ≤ (50 : ℝ) := by
    rw [show (792 : ℝ) ^ 6 * (100000000000720 : ℝ) * exp (-(22 : ℝ)) / (770 : ℝ) ^ 7
        = ((792 : ℝ) ^ 6 * (100000000000720 : ℝ) / (770 : ℝ) ^ 7) * exp (-(22 : ℝ)) by ring]
    exact le_trans
      (mul_le_mul hAcoeff exp_neg22_small (by positivity) (by positivity))
      (by norm_num)
  have hCcoeff :
      (792 : ℝ) ^ 6 * (100000000000720 : ℝ) * (7 * (2 : ℝ) ^ 8) / (770 : ℝ) ^ 8
        ≤ (358000000000 : ℝ) := by
    norm_num
  have hC :
      (792 : ℝ) ^ 6 * (100000000000720 : ℝ) *
        (7 * (2 : ℝ) ^ 8) * exp (-(22 : ℝ)) / (770 : ℝ) ^ 8 ≤ (110 : ℝ) := by
    rw [show (792 : ℝ) ^ 6 * (100000000000720 : ℝ) *
          (7 * (2 : ℝ) ^ 8) * exp (-(22 : ℝ)) / (770 : ℝ) ^ 8
        = ((792 : ℝ) ^ 6 * (100000000000720 : ℝ) * (7 * (2 : ℝ) ^ 8) /
              (770 : ℝ) ^ 8) * exp (-(22 : ℝ)) by ring]
    exact le_trans
      (mul_le_mul hCcoeff exp_neg22_small (by positivity) (by positivity))
      (by norm_num)
  have hB :
      (792 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 *
        (exp (-(407 : ℝ)) / (log 2) ^ 8) ≤ (1 : ℝ) := by
    have hBcoeff0 :
        (792 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 ≤ (2e32 : ℝ) := by
      norm_num
    have hBcoeff :
        (792 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 / (log 2) ^ 8 ≤ (2e35 : ℝ) := by
      rw [show (792 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 / (log 2) ^ 8
          = ((792 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7) * (1 / (log 2) ^ 8) by ring]
      nlinarith [inv_log2_pow8_le_1000, hBcoeff0]
    rw [show (792 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 *
          (exp (-(407 : ℝ)) / (log 2) ^ 8)
        = ((792 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 / (log 2) ^ 8) *
            exp (-(407 : ℝ)) by ring]
    exact le_trans
      (mul_le_mul hBcoeff exp_neg407_small (by positivity) (by positivity))
      (by norm_num)
  have hrewrite :
      (792 : ℝ) ^ 6 * (100000000000720 : ℝ) *
        (exp (-(22 : ℝ)) / (770 : ℝ) ^ 7
          + 7 * (exp (-(407 : ℝ)) / (log 2) ^ 8
            + (2 : ℝ) ^ 8 * exp (-(22 : ℝ)) / (770 : ℝ) ^ 8))
      = (792 : ℝ) ^ 6 * (100000000000720 : ℝ) * exp (-(22 : ℝ)) / (770 : ℝ) ^ 7
        + (792 : ℝ) ^ 6 * (100000000000720 : ℝ) * 7 *
            (exp (-(407 : ℝ)) / (log 2) ^ 8)
        + (792 : ℝ) ^ 6 * (100000000000720 : ℝ) *
            (7 * (2 : ℝ) ^ 8) * exp (-(22 : ℝ)) / (770 : ℝ) ^ 8 := by
    ring
  rw [hrewrite]
  nlinarith [hA, hB, hC]

theorem C1_le_five_million_792_of
    {a : ℝ → ℝ} {xₐ : ℝ}
    (hxₐ : xₐ = exp (792 : ℝ))
    (h2xa : 2 ≤ xₐ)
    (ha_eq_admissible_ge_two :
      ∀ {z : ℝ}, z ≥ 2 →
        a z = (log z) ^ 5 * admissible_bound 121.0961 (3 / 2) 2 5.5666305 z)
    (ha_int : IntegrableOn (fun t ↦ a t / log t ^ 7) (Set.Icc 2 xₐ) volume)
    (hJ770 :
      ∫ t in Set.Icc 2 (exp (770 : ℝ)), 1 / log t ^ 7
        ≤ exp (770 : ℝ) / log (exp (770 : ℝ)) ^ 7
          + 7 * (sqrt (exp (770 : ℝ)) / log 2 ^ 8
            + 2 ^ 8 * exp (770 : ℝ) / log (exp (770 : ℝ)) ^ 8)) :
    log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7 ≤ (5000000 : ℝ) := by
  have h770le : exp (770 : ℝ) ≤ xₐ := by
    rw [hxₐ]
    exact exp_le_exp.mpr (by norm_num)
  let K : ℝ := (100000000000720 : ℝ)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  let f : ℝ → ℝ := fun t ↦ (720 + a t) / log t ^ 7
  have hJ_int : IntegrableOn (fun t : ℝ ↦ 1 / log t ^ 7) (Set.Icc 2 xₐ) volume :=
    ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
      (continuousOn_log.mono <| by
        intro t ht
        exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) (by
      intro t ht
      exact pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1]))
  have hconst_int : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ 7) (Set.Icc 2 xₐ) volume := by
    have htmp : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) * (1 / log t ^ 7)) (Set.Icc 2 xₐ) volume :=
      hJ_int.const_mul 720
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring
  have hadd_int :
      IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ 7 + a t / log t ^ 7) (Set.Icc 2 xₐ) volume :=
    hconst_int.add ha_int
  have hf_int : IntegrableOn f (Set.Icc 2 xₐ) volume := by
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 hadd_int
    intro t ht
    dsimp [f]
    ring
  have hsplit :
      ∫ t in Set.Icc 2 xₐ, f t
        = (∫ t in Set.Icc 2 (exp (770 : ℝ)), f t)
          + (∫ t in Set.Icc (exp (770 : ℝ)) xₐ, f t) :=
    integral_Icc_split (f := f) (a := 2) (b := exp (770 : ℝ)) (c := xₐ)
      (by linarith [add_one_le_exp (770 : ℝ)]) h770le hf_int

  have hf_int_low : IntegrableOn f (Set.Icc 2 (exp (770 : ℝ))) volume :=
    hf_int.mono_set (by intro t ht; exact ⟨ht.1, le_trans ht.2 h770le⟩)
  have hlow_rhs_int :
      IntegrableOn (fun t : ℝ ↦ K / log t ^ 7) (Set.Icc 2 (exp (770 : ℝ))) volume := by
    have htmp :
        IntegrableOn (fun t : ℝ ↦ K * (1 / log t ^ 7)) (Set.Icc 2 (exp (770 : ℝ))) volume :=
      (ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
        (continuousOn_log.mono <| by
          intro t ht
          exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) (by
        intro t ht
        exact pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1]))).const_mul K
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring
  have hlow_pt : ∀ t ∈ Set.Icc 2 (exp (770 : ℝ)), f t ≤ K / log t ^ 7 := by
    intro t ht
    have ha_le : a t ≤ (100000000000000 : ℝ) := a_low_huge_of ha_eq_admissible_ge_two (by
      exact ⟨ht.1, le_trans ht.2 (exp_le_exp.mpr (by norm_num))⟩)
    have hnum_le : 720 + a t ≤ K := by
      dsimp [K]
      linarith
    have hlog_nonneg : 0 ≤ log t := log_nonneg (by linarith [ht.1])
    dsimp [f]
    exact div_le_div_of_nonneg_right hnum_le (pow_nonneg hlog_nonneg 7)
  have hlow_le_rhs :
      ∫ t in Set.Icc 2 (exp (770 : ℝ)), f t
        ≤ ∫ t in Set.Icc 2 (exp (770 : ℝ)), K / log t ^ 7 :=
    MeasureTheory.setIntegral_mono_on hf_int_low hlow_rhs_int measurableSet_Icc hlow_pt
  have hlow_factor :
      ∫ t in Set.Icc 2 (exp (770 : ℝ)), K / log t ^ 7
        = K * ∫ t in Set.Icc 2 (exp (770 : ℝ)), 1 / log t ^ 7 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    ring
  have hlow_le :
      ∫ t in Set.Icc 2 (exp (770 : ℝ)), f t
        ≤ K * (exp (770 : ℝ) / log (exp (770 : ℝ)) ^ 7
          + 7 * (sqrt (exp (770 : ℝ)) / log 2 ^ 8
            + 2 ^ 8 * exp (770 : ℝ) / log (exp (770 : ℝ)) ^ 8)) := by
    rw [hlow_factor] at hlow_le_rhs
    exact le_trans hlow_le_rhs (mul_le_mul_of_nonneg_left hJ770 hK_nonneg)

  have hf_int_high : IntegrableOn f (Set.Icc (exp (770 : ℝ)) xₐ) volume :=
    hf_int.mono_set (by
      intro t ht
      exact ⟨le_trans (by linarith [add_one_le_exp (770 : ℝ)]) ht.1, ht.2⟩)
  have hconst_high_int :
      IntegrableOn (fun _ : ℝ ↦ (3250000720 : ℝ) / (770 : ℝ) ^ 7) (Set.Icc (exp (770 : ℝ)) xₐ) volume :=
    ContinuousOn.integrableOn_Icc continuousOn_const
  have ha_mono_770 : AntitoneOn a (Set.Ici (exp (770 : ℝ))) := by
    intro x hx y hy hxy
    exact (a_mono_of ha_eq_admissible_ge_two)
      (Set.mem_Ici.mpr <| le_trans (exp_le_exp.mpr (by norm_num : (236 : ℝ) ≤ 770)) hx)
      (Set.mem_Ici.mpr <| le_trans (exp_le_exp.mpr (by norm_num : (236 : ℝ) ≤ 770)) hy)
      hxy
  have ha_770_upper : a (exp (770 : ℝ)) ≤ (3250000000 : ℝ) := a_770_upper_of ha_eq_admissible_ge_two
  have hhigh_pt : ∀ t ∈ Set.Icc (exp (770 : ℝ)) xₐ, f t ≤ (3250000720 : ℝ) / (770 : ℝ) ^ 7 := by
    intro t ht
    have hat770 : a t ≤ a (exp (770 : ℝ)) :=
      ha_mono_770
        (Set.mem_Ici.mpr (le_rfl : exp (770 : ℝ) ≤ exp (770 : ℝ)))
        (Set.mem_Ici.mpr ht.1) ht.1
    have hat : a t ≤ (3250000000 : ℝ) := le_trans hat770 ha_770_upper
    have hnum_le : 720 + a t ≤ (3250000720 : ℝ) := by
      linarith
    have hlog_ge : (770 : ℝ) ≤ log t := by
      have h := log_le_log (by positivity : (0 : ℝ) < exp (770 : ℝ)) ht.1
      simpa [log_exp] using h
    have hpow : (770 : ℝ) ^ 7 ≤ log t ^ 7 := pow_le_pow_left₀ (by norm_num) hlog_ge 7
    have hlog_nonneg : 0 ≤ log t := by linarith [hlog_ge]
    calc
      f t = (720 + a t) / log t ^ 7 := rfl
      _ ≤ (3250000720 : ℝ) / log t ^ 7 := by
        exact div_le_div_of_nonneg_right hnum_le (pow_nonneg hlog_nonneg 7)
      _ ≤ (3250000720 : ℝ) / (770 : ℝ) ^ 7 := by
        exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (3250000720 : ℝ)) (by positivity) hpow
  have hhigh_le_const :
      ∫ t in Set.Icc (exp (770 : ℝ)) xₐ, f t
        ≤ ∫ t in Set.Icc (exp (770 : ℝ)) xₐ, (3250000720 : ℝ) / (770 : ℝ) ^ 7 :=
    MeasureTheory.setIntegral_mono_on hf_int_high hconst_high_int measurableSet_Icc hhigh_pt
  have hhigh_const_eval :
      ∫ t in Set.Icc (exp (770 : ℝ)) xₐ, (3250000720 : ℝ) / (770 : ℝ) ^ 7
        = (3250000720 : ℝ) / (770 : ℝ) ^ 7 * (xₐ - exp (770 : ℝ)) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h770le,
      intervalIntegral.integral_const]
    simp [smul_eq_mul, mul_comm]
  have hhigh_le :
      ∫ t in Set.Icc (exp (770 : ℝ)) xₐ, f t
        ≤ (3250000720 : ℝ) / (770 : ℝ) ^ 7 * xₐ := by
    have hstep :
        (3250000720 : ℝ) / (770 : ℝ) ^ 7 * (xₐ - exp (770 : ℝ))
          ≤ (3250000720 : ℝ) / (770 : ℝ) ^ 7 * xₐ := by
      exact mul_le_mul_of_nonneg_left
        (by linarith [show (0 : ℝ) ≤ exp (770 : ℝ) by positivity]) (by positivity)
    calc
      ∫ t in Set.Icc (exp (770 : ℝ)) xₐ, f t
        ≤ (3250000720 : ℝ) / (770 : ℝ) ^ 7 * (xₐ - exp (770 : ℝ)) := by
            simpa [hhigh_const_eval] using hhigh_le_const
      _ ≤ (3250000720 : ℝ) / (770 : ℝ) ^ 7 * xₐ := hstep

  have hmain :
      log xₐ ^ 6 / xₐ *
          ((∫ t in Set.Icc 2 (exp (770 : ℝ)), f t) + (∫ t in Set.Icc (exp (770 : ℝ)) xₐ, f t))
        ≤ log xₐ ^ 6 / xₐ *
            (K * (exp (770 : ℝ) / log (exp (770 : ℝ)) ^ 7
              + 7 * (sqrt (exp (770 : ℝ)) / log 2 ^ 8
                + 2 ^ 8 * exp (770 : ℝ) / log (exp (770 : ℝ)) ^ 8))
              + (3250000720 : ℝ) / (770 : ℝ) ^ 7 * xₐ) :=
    mul_le_mul_of_nonneg_left (by linarith [hlow_le, hhigh_le]) (by positivity)
  have hmain' :
      (792 : ℝ) ^ 6 / exp (792 : ℝ) *
          ((∫ t in Set.Icc 2 (exp (770 : ℝ)), f t)
            + (∫ t in Set.Icc (exp (770 : ℝ)) (exp (792 : ℝ)), f t))
        ≤ (792 : ℝ) ^ 6 / exp (792 : ℝ) *
          (K * (exp (770 : ℝ) / (770 : ℝ) ^ 7
            + 7 * (sqrt (exp (770 : ℝ)) / log 2 ^ 8
              + 2 ^ 8 * exp (770 : ℝ) / (770 : ℝ) ^ 8))
            + (3250000720 : ℝ) / (770 : ℝ) ^ 7 * exp (792 : ℝ)) := by
    simpa [hxₐ, log_exp] using hmain
  have hdecomp :
      (792 : ℝ) ^ 6 / exp (792 : ℝ) *
          (K * (exp (770 : ℝ) / (770 : ℝ) ^ 7
            + 7 * (sqrt (exp (770 : ℝ)) / log 2 ^ 8
              + 2 ^ 8 * exp (770 : ℝ) / (770 : ℝ) ^ 8))
            + (3250000720 : ℝ) / (770 : ℝ) ^ 7 * exp (792 : ℝ))
        = (792 : ℝ) ^ 6 / exp (792 : ℝ) *
            (K * (exp (770 : ℝ) / (770 : ℝ) ^ 7
              + 7 * (sqrt (exp (770 : ℝ)) / log 2 ^ 8
                + 2 ^ 8 * exp (770 : ℝ) / (770 : ℝ) ^ 8)))
          + (3250000720 : ℝ) * (792 : ℝ) ^ 6 / (770 : ℝ) ^ 7 := by
    field_simp
  rw [hdecomp] at hmain'
  have hlow_fin :
      (792 : ℝ) ^ 6 / exp (792 : ℝ) *
          (K * (exp (770 : ℝ) / (770 : ℝ) ^ 7
            + 7 * (sqrt (exp (770 : ℝ)) / log 2 ^ 8
              + 2 ^ 8 * exp (770 : ℝ) / (770 : ℝ) ^ 8))) ≤ (200 : ℝ) := by
    rw [sqrt_exp_770]
    have h22 : exp (770 : ℝ) / exp (792 : ℝ) = exp (-(22 : ℝ)) := by
      have h := (exp_sub (770 : ℝ) (792 : ℝ)).symm
      simpa [show (770 : ℝ) - 792 = (-(22 : ℝ)) by norm_num] using h
    have h407 : exp (385 : ℝ) / exp (792 : ℝ) = exp (-(407 : ℝ)) := by
      have h := (exp_sub (385 : ℝ) (792 : ℝ)).symm
      simpa [show (385 : ℝ) - 792 = (-(407 : ℝ)) by norm_num] using h
    have hrewrite :
        (792 : ℝ) ^ 6 / exp (792 : ℝ) *
            (K * (exp (770 : ℝ) / (770 : ℝ) ^ 7
              + 7 * (exp (385 : ℝ) / log 2 ^ 8
                + 2 ^ 8 * exp (770 : ℝ) / (770 : ℝ) ^ 8)))
          = (792 : ℝ) ^ 6 * K *
              (exp (-(22 : ℝ)) / (770 : ℝ) ^ 7
                + 7 * (exp (-(407 : ℝ)) / (log 2) ^ 8
                  + (2 : ℝ) ^ 8 * exp (-(22 : ℝ)) / (770 : ℝ) ^ 8)) := by
      rw [← h22, ← h407]
      field_simp [K]
    rw [hrewrite]
    dsimp [K]
    exact low_contrib_raw_le_two_hundred_792_770
  have hhigh_fin :
      (3250000720 : ℝ) * (792 : ℝ) ^ 6 / (770 : ℝ) ^ 7 ≤ (4999000 : ℝ) := by
    norm_num
  have hfin :
      (792 : ℝ) ^ 6 / exp (792 : ℝ) *
          (K * (exp (770 : ℝ) / (770 : ℝ) ^ 7
            + 7 * (sqrt (exp (770 : ℝ)) / log 2 ^ 8
              + 2 ^ 8 * exp (770 : ℝ) / (770 : ℝ) ^ 8)))
        + (3250000720 : ℝ) * (792 : ℝ) ^ 6 / (770 : ℝ) ^ 7 ≤ (5000000 : ℝ) := by
    nlinarith [hlow_fin, hhigh_fin]
  exact le_trans (by rw [hsplit]; simpa [f, hxₐ, log_exp] using hmain') hfin

theorem M_upper_from_coarse_bounds
    {a_xa a_exa C1 B : ℝ}
    (hax0 : 0 ≤ a_xa) (hC1 : C1 ≤ (78730000000 : ℝ))
    (hax : a_xa ≤ (171243 : ℝ)) (haex : a_exa ≤ (170214 : ℝ))
    (hB : B ≤ (1 : ℝ)) :
    120 + a_exa + C1 + (720 + a_xa) * B ≤ (78800000000 : ℝ) := by
  have hBterm : (720 + a_xa) * B ≤ (171963 : ℝ) := by
    have hsum : 720 + a_xa ≤ (171963 : ℝ) := by
      linarith
    have h720_nonneg : 0 ≤ 720 + a_xa := by linarith
    exact le_trans (mul_le_mul_of_nonneg_left hB h720_nonneg) (by simpa using hsum)
  nlinarith [hC1, haex, hBterm]

end FKS14Calculations

end Ramanujan
