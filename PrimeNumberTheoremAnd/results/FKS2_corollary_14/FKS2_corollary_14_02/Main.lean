import PrimeNumberTheoremAnd.Ramanujan
import PrimeNumberTheoremAnd.FKS2
import PrimeNumberTheoremAnd.results.FKS2_corollary_14.FKS2_corollary_14_02.Calculations
import LeanCert.Tactic.IntervalAuto

namespace RamanujanFKS14

open Real Set MeasureTheory intervalIntegral Chebyshev

noncomputable def xₐ : ℝ := exp (792 : ℝ)

noncomputable def exₐ : ℝ := exp (793 : ℝ)

noncomputable def a (x : ℝ) : ℝ :=
  log x ^ (5 : ℕ) * admissible_bound 121.0961 (3 / 2 : ℝ) 2 5.5666305 x

noncomputable def B : ℝ :=
  1 / log xₐ + 7 * 2 ^ (8 : ℕ) / log xₐ ^ (2 : ℕ)
    + 7 * log xₐ ^ (6 : ℕ) / (sqrt xₐ * log 2 ^ (8 : ℕ))

noncomputable def C₁ : ℝ :=
  log xₐ ^ (6 : ℕ) / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ (7 : ℕ)

noncomputable def mₐ : ℝ := 5629000000

noncomputable def Mₐ : ℝ := 2800000000

private theorem xₐ_pos : 0 < xₐ := by
  unfold xₐ
  positivity

private theorem exₐ_pos : 0 < exₐ := by
  unfold exₐ
  positivity

private theorem one_lt_xₐ : 1 < xₐ := by
  unfold xₐ
  exact Real.one_lt_exp_iff.2 (by norm_num)

private theorem two_le_xₐ : 2 ≤ xₐ := by
  unfold xₐ
  have h : (2 : ℝ) < exp (1 : ℝ) := by
    nlinarith [Real.exp_one_gt_d9]
  have h' : exp (1 : ℝ) ≤ exp (792 : ℝ) := by
    exact exp_le_exp.mpr (by norm_num)
  linarith

private theorem two_le_exₐ : 2 ≤ exₐ := by
  unfold exₐ
  have h : (2 : ℝ) < exp (1 : ℝ) := by
    nlinarith [Real.exp_one_gt_d9]
  have h' : exp (1 : ℝ) ≤ exp (793 : ℝ) := by
    exact exp_le_exp.mpr (by norm_num)
  linarith

private theorem two_le_exp_770 : 2 ≤ exp (770 : ℝ) := by
  have h : (2 : ℝ) < exp (1 : ℝ) := by
    nlinarith [Real.exp_one_gt_d9]
  have h' : exp (1 : ℝ) ≤ exp (770 : ℝ) := by
    exact exp_le_exp.mpr (by norm_num)
  linarith

private theorem xₐ_le_exₐ : xₐ ≤ exₐ := by
  unfold xₐ exₐ
  exact exp_le_exp.mpr (by norm_num)

private theorem exₐ_eq : exₐ = exp 1 * xₐ := by
  unfold exₐ xₐ
  rw [← exp_add]
  norm_num

private theorem log_xₐ_val : log xₐ = (792 : ℝ) := by
  rw [xₐ, log_exp]

private theorem log_xₐ_pos : 0 < log xₐ := by
  rw [log_xₐ_val]
  norm_num

private theorem exₐ_ge_e_xₐ : exₐ ≥ exp 1 * xₐ := by
  rw [exₐ_eq]

private lemma theta_bound (x : ℝ) (hx : 2 ≤ x) :
    |θ x - x| * log x ^ (5 : ℕ) ≤ x * a x := by
  have hx0 : 0 < x := by
    linarith
  have hE : Eθ x ≤ admissible_bound 121.0961 (3 / 2 : ℝ) 2 5.5666305 x :=
    FKS2.corollary_14 x hx
  unfold Eθ at hE
  have hmain : |θ x - x| ≤ x * admissible_bound 121.0961 (3 / 2 : ℝ) 2 5.5666305 x := by
    simpa [mul_comm] using (div_le_iff₀ hx0).mp hE
  have hlog5_nonneg : 0 ≤ log x ^ (5 : ℕ) := by
    exact pow_nonneg (log_nonneg (by linarith : (1 : ℝ) ≤ x)) 5
  have hmul := mul_le_mul_of_nonneg_right hmain hlog5_nonneg
  simpa [a, mul_assoc, mul_left_comm, mul_comm] using hmul

private lemma integral_Icc_split_at_xa
    (f : ℝ → ℝ)
    (x : ℝ)
    (hxax : xₐ ≤ x)
    (hInt : IntegrableOn f (Set.Icc 2 x) volume) :
    ∫ t in Set.Icc 2 x, f t = (∫ t in Set.Icc 2 xₐ, f t) + (∫ t in Set.Icc xₐ x, f t) := by
  exact Ramanujan.integral_Icc_split (f := f) (a := 2) (b := xₐ) (c := x)
    two_le_xₐ hxax hInt

private lemma h_monotone_aux : MonotoneOn (fun y : ℝ => y - 12 * log y) (Set.Ici 12) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 12) ?_ ?_ ?_
  · exact continuousOn_id.sub (continuousOn_const.mul
      (continuousOn_log.mono (by
        intro y hy
        exact ne_of_gt (lt_of_lt_of_le (by norm_num) (Set.mem_Ici.mp hy)))))
  · intro y hy
    rw [interior_Ici] at hy
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((hasDerivAt_id y).sub
      ((Real.hasDerivAt_log (show y ≠ 0 by linarith [Set.mem_Ioi.mp hy])).const_mul 12)).differentiableAt
  · intro y hy
    rw [interior_Ici] at hy
    have hypos : 0 < y := by
      linarith [Set.mem_Ioi.mp hy]
    have hderiv : deriv (fun y : ℝ => y - 12 * log y) y = 1 - 12 * y⁻¹ :=
      ((hasDerivAt_id y).sub
        ((Real.hasDerivAt_log (show y ≠ 0 by linarith [hypos])).const_mul 12)).deriv
    rw [hderiv]
    have hyge12 : 12 ≤ y := le_of_lt (Set.mem_Ioi.mp hy)
    have hyinv : 12 * y⁻¹ ≤ 1 := by
      have hdiv : 12 / y ≤ 1 := (div_le_iff₀ hypos).2 (by simpa using hyge12)
      simpa [div_eq_mul_inv] using hdiv
    nlinarith

private lemma ratio_bound_xa (x : ℝ) (hxax : xₐ ≤ x) :
    xₐ / log xₐ ^ (12 : ℕ) ≤ x / log x ^ (12 : ℕ) := by
  have hxpos : 0 < x := lt_of_lt_of_le xₐ_pos hxax
  have h1x : 1 < x := lt_of_lt_of_le one_lt_xₐ hxax
  have hlogapos : 0 < log xₐ := log_xₐ_pos
  have hlogpos : 0 < log x := log_pos h1x
  have hlogxa_le : log xₐ ≤ log x := log_le_log xₐ_pos hxax
  have hlogxa_ge12 : 12 ≤ log xₐ := by
    rw [log_xₐ_val]
    norm_num
  have hlogx_ge12 : 12 ≤ log x := le_trans hlogxa_ge12 hlogxa_le
  have hh : log xₐ - 12 * log (log xₐ) ≤ log x - 12 * log (log x) :=
    h_monotone_aux (Set.mem_Ici.mpr hlogxa_ge12) (Set.mem_Ici.mpr hlogx_ge12) hlogxa_le
  have hleft_pos : 0 < xₐ / log xₐ ^ (12 : ℕ) := by
    exact div_pos xₐ_pos (pow_pos log_xₐ_pos 12)
  have hright_pos : 0 < x / log x ^ (12 : ℕ) := by
    exact div_pos hxpos (pow_pos hlogpos 12)
  rw [← log_le_log_iff hleft_pos hright_pos]
  have hleft : log (xₐ / log xₐ ^ (12 : ℕ)) = log xₐ - 12 * log (log xₐ) := by
    rw [log_div xₐ_pos.ne' (pow_ne_zero _ hlogapos.ne'), log_pow]
    ring
  have hright : log (x / log x ^ (12 : ℕ)) = log x - 12 * log (log x) := by
    rw [log_div hxpos.ne' (pow_ne_zero _ hlogpos.ne'), log_pow]
    ring
  linarith

private lemma ratio6_bound_xa (x : ℝ) (hxax : xₐ ≤ x) :
    xₐ / log xₐ ^ (6 : ℕ) ≤ x / log x ^ (6 : ℕ) := by
  have hxpos : 0 < x := lt_of_lt_of_le xₐ_pos hxax
  have h1x : 1 < x := lt_of_lt_of_le one_lt_xₐ hxax
  have hlogapos : 0 < log xₐ := log_xₐ_pos
  have hlogpos : 0 < log x := log_pos h1x
  have hlogxa_le : log xₐ ≤ log x := log_le_log xₐ_pos hxax
  have hlogxa_ge12 : 12 ≤ log xₐ := by
    rw [log_xₐ_val]
    norm_num
  have hlogx_ge12 : 12 ≤ log x := le_trans hlogxa_ge12 hlogxa_le
  have hh : log xₐ - 6 * log (log xₐ) ≤ log x - 6 * log (log x) := by
    have hmono6 : MonotoneOn (fun y : ℝ => y - 6 * log y) (Set.Ici 6) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 6) ?_ ?_ ?_
      · exact continuousOn_id.sub (continuousOn_const.mul
          (continuousOn_log.mono (by
            intro y hy
            exact ne_of_gt (lt_of_lt_of_le (by norm_num) (Set.mem_Ici.mp hy)))))
      · intro y hy
        rw [interior_Ici] at hy
        refine DifferentiableAt.differentiableWithinAt ?_
        exact ((hasDerivAt_id y).sub
          ((Real.hasDerivAt_log (show y ≠ 0 by linarith [Set.mem_Ioi.mp hy])).const_mul 6)).differentiableAt
      · intro y hy
        rw [interior_Ici] at hy
        have hypos : 0 < y := by
          linarith [Set.mem_Ioi.mp hy]
        have hderiv : deriv (fun y : ℝ => y - 6 * log y) y = 1 - 6 * y⁻¹ :=
          ((hasDerivAt_id y).sub
            ((Real.hasDerivAt_log (show y ≠ 0 by linarith [hypos])).const_mul 6)).deriv
        rw [hderiv]
        have hyge6 : 6 ≤ y := le_of_lt (Set.mem_Ioi.mp hy)
        have hyinv : 6 * y⁻¹ ≤ 1 := by
          have hdiv : 6 / y ≤ 1 := (div_le_iff₀ hypos).2 (by simpa using hyge6)
          simpa [div_eq_mul_inv] using hdiv
        nlinarith
    have hlogxa_ge6 : 6 ≤ log xₐ := le_trans (by norm_num) hlogxa_ge12
    have hlogx_ge6 : 6 ≤ log x := le_trans (by norm_num) hlogx_ge12
    exact hmono6 (Set.mem_Ici.mpr hlogxa_ge6) (Set.mem_Ici.mpr hlogx_ge6) hlogxa_le
  have hleft_pos : 0 < xₐ / log xₐ ^ (6 : ℕ) := by
    exact div_pos xₐ_pos (pow_pos log_xₐ_pos 6)
  have hright_pos : 0 < x / log x ^ (6 : ℕ) := by
    exact div_pos hxpos (pow_pos hlogpos 6)
  rw [← log_le_log_iff hleft_pos hright_pos]
  have hleft : log (xₐ / log xₐ ^ (6 : ℕ)) = log xₐ - 6 * log (log xₐ) := by
    rw [log_div xₐ_pos.ne' (pow_ne_zero _ hlogapos.ne'), log_pow]
    ring
  have hright : log (x / log x ^ (6 : ℕ)) = log x - 6 * log (log x) := by
    rw [log_div hxpos.ne' (pow_ne_zero _ hlogpos.ne'), log_pow]
    ring
  linarith

private lemma sqrt_bound_xa (x : ℝ) (hxax : xₐ ≤ x) :
    sqrt x ≤ x / log x ^ (6 : ℕ) * log xₐ ^ (6 : ℕ) / sqrt xₐ := by
  have hxpos : 0 < x := lt_of_lt_of_le xₐ_pos hxax
  have h1x : 1 < x := lt_of_lt_of_le one_lt_xₐ hxax
  have hlogpos : 0 < log x := log_pos h1x
  have hlogapos : 0 < log xₐ := log_xₐ_pos
  have hr : xₐ / log xₐ ^ (12 : ℕ) ≤ x / log x ^ (12 : ℕ) := ratio_bound_xa x hxax
  apply sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h1 : xₐ ≤ x * log xₐ ^ (12 : ℕ) / log x ^ (12 : ℕ) := by
    have hloga12_pos : 0 < log xₐ ^ (12 : ℕ) := by positivity
    have := (div_le_iff₀ hloga12_pos).mp hr
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hr' : x * xₐ ≤ x ^ (2 : ℕ) * log xₐ ^ (12 : ℕ) / log x ^ (12 : ℕ) := by
    have hm : x * xₐ ≤ x * (x * log xₐ ^ (12 : ℕ) / log x ^ (12 : ℕ)) :=
      mul_le_mul_of_nonneg_left h1 hxpos.le
    have hmul : x * (x * log xₐ ^ (12 : ℕ) / log x ^ (12 : ℕ)) =
        x ^ (2 : ℕ) * log xₐ ^ (12 : ℕ) / log x ^ (12 : ℕ) := by
      ring
    simpa [hmul] using hm
  have hsqrtxa_ne : sqrt xₐ ≠ 0 := ne_of_gt (sqrt_pos.mpr xₐ_pos)
  have hsq' : (sqrt xₐ) ^ (2 : ℕ) = xₐ := by
    simpa [pow_two] using (sq_sqrt xₐ_pos.le)
  have hcalc1 :
      (x / log x ^ (6 : ℕ) * log xₐ ^ (6 : ℕ) / sqrt xₐ) ^ (2 : ℕ) =
        x ^ (2 : ℕ) * log xₐ ^ (12 : ℕ) / (log x ^ (12 : ℕ) * (sqrt xₐ) ^ (2 : ℕ)) := by
    field_simp [hlogpos.ne', hlogapos.ne', hsqrtxa_ne]
  rw [hcalc1, hsq']
  have : x * (log x ^ (12 : ℕ) * xₐ) ≤ x ^ (2 : ℕ) * log xₐ ^ (12 : ℕ) := by
    have hmul : x * xₐ * log x ^ (12 : ℕ) ≤
        (x ^ (2 : ℕ) * log xₐ ^ (12 : ℕ) / log x ^ (12 : ℕ)) * log x ^ (12 : ℕ) :=
      mul_le_mul_of_nonneg_right hr' (by positivity)
    have hlog12_ne : log x ^ (12 : ℕ) ≠ 0 := pow_ne_zero _ hlogpos.ne'
    have htmp : (x ^ (2 : ℕ) * log xₐ ^ (12 : ℕ) / log x ^ (12 : ℕ)) * log x ^ (12 : ℕ) =
        x ^ (2 : ℕ) * log xₐ ^ (12 : ℕ) := by
      field_simp [hlog12_ne]
    nlinarith
  have hden_pos : 0 < log x ^ (12 : ℕ) * xₐ := by
    exact mul_pos (pow_pos hlogpos 12) xₐ_pos
  exact (le_div_iff₀ hden_pos).2 <| by
    simpa [mul_assoc, mul_left_comm, mul_comm] using this

private lemma sqrt_term_bound_xa (x : ℝ) (hxax : xₐ ≤ x) :
    sqrt x / log 2 ^ (8 : ℕ) ≤
      x / log x ^ (6 : ℕ) * (log xₐ ^ (6 : ℕ) / (sqrt xₐ * log 2 ^ (8 : ℕ))) := by
  have hsqrt := sqrt_bound_xa x hxax
  have := mul_le_mul_of_nonneg_right hsqrt (show 0 ≤ (log 2 ^ (8 : ℕ))⁻¹ by positivity)
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

private lemma pi_upper_specific_h720Ia
    (x : ℝ)
    (ha_int : IntegrableOn (fun t ↦ a t / log t ^ (7 : ℕ)) (Set.Icc 2 x) volume) :
    (720 : ℝ) * (∫ t in Set.Icc 2 x, 1 / log t ^ (7 : ℕ))
      + (∫ t in Set.Icc 2 x, a t / log t ^ (7 : ℕ))
      = ∫ t in Set.Icc 2 x, (720 + a t) / log t ^ (7 : ℕ) := by
  have hJ_int : IntegrableOn (fun t : ℝ ↦ 1 / log t ^ (7 : ℕ)) (Set.Icc 2 x) volume :=
    ContinuousOn.integrableOn_Icc (continuousOn_const.div
      (ContinuousOn.pow
        (continuousOn_log.mono <| by
          intro t ht
          exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) fun t ht ↦
          pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1])
  have h720_int_mul :
      IntegrableOn (fun t : ℝ ↦ (720 : ℝ) * (1 / log t ^ (7 : ℕ))) (Set.Icc 2 x) volume :=
    hJ_int.const_mul 720
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add h720_int_mul ha_int]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
  intro t ht
  ring

private lemma pi_upper_specific_main_le
    (x : ℝ)
    (hx2 : 2 ≤ x)
    (hpi0 :
      pi x ≤ x / log x + a x * x / log x ^ (6 : ℕ) + (∫ t in Set.Icc 2 x, 1 / log t ^ (2 : ℕ))
        + ∫ t in Set.Icc 2 x, a t / log t ^ (7 : ℕ))
    (hI2 :
      ∫ t in Set.Icc 2 x, 1 / log t ^ (2 : ℕ) =
        x / log x ^ (2 : ℕ) + 2 * x / log x ^ (3 : ℕ) + 6 * x / log x ^ (4 : ℕ)
          + 24 * x / log x ^ (5 : ℕ) + 120 * x / log x ^ (6 : ℕ)
          - 2 * (∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1))
          + 720 * ∫ t in Set.Icc 2 x, 1 / log t ^ (7 : ℕ))
    (hsumx :
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) =
        x / log x + x / log x ^ (2 : ℕ) + 2 * x / log x ^ (3 : ℕ)
          + 6 * x / log x ^ (4 : ℕ) + 24 * x / log x ^ (5 : ℕ))
    (hS_nonneg : 0 ≤ (∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)))
    (hax_le : a x ≤ a exₐ)
    (h720Ia :
      (720 : ℝ) * (∫ t in Set.Icc 2 x, 1 / log t ^ (7 : ℕ))
        + (∫ t in Set.Icc 2 x, a t / log t ^ (7 : ℕ))
        = ∫ t in Set.Icc 2 x, (720 + a t) / log t ^ (7 : ℕ)) :
    pi x ≤ x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
      + ((120 + a exₐ) * x / log x ^ (6 : ℕ))
      + (∫ t in Set.Icc 2 x, (720 + a t) / log t ^ (7 : ℕ)) := by
  let S : ℝ := ∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)
  let J : ℝ := ∫ t in Set.Icc 2 x, 1 / log t ^ (7 : ℕ)
  let IA : ℝ := ∫ t in Set.Icc 2 x, a t / log t ^ (7 : ℕ)
  let Q : ℝ :=
    x / log x ^ (2 : ℕ) + 2 * x / log x ^ (3 : ℕ) + 6 * x / log x ^ (4 : ℕ)
      + 24 * x / log x ^ (5 : ℕ) + 120 * x / log x ^ (6 : ℕ)
  let P : ℝ :=
    x / log x + x / log x ^ (2 : ℕ) + 2 * x / log x ^ (3 : ℕ)
      + 6 * x / log x ^ (4 : ℕ) + 24 * x / log x ^ (5 : ℕ)
  have htmp :
      pi x ≤ x / log x + a x * x / log x ^ (6 : ℕ)
        + (x / log x ^ (2 : ℕ) + 2 * x / log x ^ (3 : ℕ) + 6 * x / log x ^ (4 : ℕ)
          + 24 * x / log x ^ (5 : ℕ) + 120 * x / log x ^ (6 : ℕ)
          - 2 * S + 720 * J)
        + IA := by
    have htmp0 := hpi0
    rw [hI2] at htmp0
    simpa [S, J, IA] using htmp0
  have htmp2 :
      pi x ≤ P + (120 + a exₐ) * x / log x ^ (6 : ℕ) + (720 * J + IA) := by
    have haxterm : a x * x / log x ^ (6 : ℕ) ≤ a exₐ * x / log x ^ (6 : ℕ) := by
      have hxlog6_nonneg : 0 ≤ x / log x ^ (6 : ℕ) :=
        div_nonneg (by linarith) (pow_nonneg (log_nonneg (by linarith)) 6)
      have hmul : a x * (x / log x ^ (6 : ℕ)) ≤ a exₐ * (x / log x ^ (6 : ℕ)) :=
        mul_le_mul_of_nonneg_right hax_le hxlog6_nonneg
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
    have hdropS : Q - 2 * S + 720 * J ≤ Q + 720 * J := by
      linarith
    have hmidJ :
        x / log x + a x * x / log x ^ (6 : ℕ) + (Q - 2 * S + 720 * J) + IA
          ≤ x / log x + a exₐ * x / log x ^ (6 : ℕ) + (Q + 720 * J) + IA := by
      have h1 : x / log x + a x * x / log x ^ (6 : ℕ) ≤
          x / log x + a exₐ * x / log x ^ (6 : ℕ) :=
        add_le_add_right haxterm (x / log x)
      have h2 : (Q - 2 * S + 720 * J) + IA ≤ (Q + 720 * J) + IA :=
        add_le_add_left hdropS IA
      have hsum := add_le_add h1 h2
      simpa [add_assoc] using hsum
    have htmp2raw :
        pi x ≤ x / log x + a exₐ * x / log x ^ (6 : ℕ) + (Q + 720 * J) + IA :=
      le_trans (by
        unfold Q
        simpa [J, IA] using htmp) hmidJ
    have hEq :
        x / log x + a exₐ * x / log x ^ (6 : ℕ) + (Q + 720 * J) + IA =
          P + (120 + a exₐ) * x / log x ^ (6 : ℕ) + (720 * J + IA) := by
      unfold P Q
      ring
    simpa [hEq] using htmp2raw
  let G : ℝ := ∫ t in Set.Icc 2 x, (720 + a t) / log t ^ (7 : ℕ)
  have htmp3 : pi x ≤ P + (120 + a exₐ) * x / log x ^ (6 : ℕ) + G := by
    have h720IaJ : (720 : ℝ) * J + IA = G := by
      unfold G J IA
      simpa using h720Ia
    calc
      pi x ≤ P + (120 + a exₐ) * x / log x ^ (6 : ℕ) + (720 * J + IA) := htmp2
      _ = P + (120 + a exₐ) * x / log x ^ (6 : ℕ) + G := by rw [h720IaJ]
  have hsum_form :
      P = x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) := by
    unfold P
    exact hsumx.symm
  calc
    pi x ≤ P + (120 + a exₐ) * x / log x ^ (6 : ℕ) + G := htmp3
    _ = x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
          + (120 + a exₐ) * x / log x ^ (6 : ℕ) + G := by rw [hsum_form]
    _ = x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
          + (120 + a exₐ) * x / log x ^ (6 : ℕ)
          + (∫ t in Set.Icc 2 x, (720 + a t) / log t ^ (7 : ℕ)) := by
      simp [G, add_assoc]

private lemma a_eq_admissible_ge_two {z : ℝ} (_hz : z ≥ 2) :
    a z = log z ^ (5 : ℕ) * admissible_bound 121.0961 (3 / 2 : ℝ) 2 5.5666305 z := by
  simp [a]

private lemma styleVal_continuousOn {L U : ℝ} :
    ContinuousOn Ramanujan.FKS14Calculations.styleVal (Set.Icc L U) := by
  unfold Ramanujan.FKS14Calculations.styleVal
  have hdiv : ContinuousOn (fun y : ℝ ↦ y / 5.5666305) (Set.Icc L U) := by
    have hmul : ContinuousOn (fun y : ℝ ↦ y * ((5.5666305 : ℝ)⁻¹)) (Set.Icc L U) :=
      continuousOn_id.mul continuousOn_const
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hmul
  have hsqrt : ContinuousOn (fun y : ℝ ↦ sqrt (y / 5.5666305)) (Set.Icc L U) := by
    simpa using continuous_sqrt.comp_continuousOn hdiv
  have hpow :
      ContinuousOn (fun y : ℝ ↦ (sqrt (y / 5.5666305)) ^ (13 : ℕ)) (Set.Icc L U) :=
    hsqrt.pow 13
  have harg :
      ContinuousOn (fun y : ℝ ↦ -(2 : ℝ) * sqrt (y / 5.5666305)) (Set.Icc L U) := by
    simpa using (continuousOn_const.mul hsqrt).neg
  have hexp :
      ContinuousOn (fun y : ℝ ↦ exp (-(2 : ℝ) * sqrt (y / 5.5666305))) (Set.Icc L U) := by
    simpa using continuous_exp.comp_continuousOn harg
  have hconst :
      ContinuousOn (fun _ : ℝ ↦ (121.0961 : ℝ) * (5.5666305 : ℝ) ^ (5 : ℕ)) (Set.Icc L U) :=
    continuousOn_const
  refine (hconst.mul (hpow.mul hexp)).congr ?_
  intro y hy
  simp [Pi.mul_apply, mul_assoc]

private theorem integrable_a_over_log7
    (x : ℝ) (hx2 : 2 ≤ x) :
    IntegrableOn (fun t ↦ a t / log t ^ (7 : ℕ)) (Set.Icc 2 x) volume := by
  have hlog :
      ContinuousOn log (Set.Icc 2 x) :=
    continuousOn_log.mono <| by
      intro t ht
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)
  have hstyle_log :
      ContinuousOn (fun t : ℝ ↦ Ramanujan.FKS14Calculations.styleVal (log t)) (Set.Icc 2 x) := by
    refine (styleVal_continuousOn (L := log 2) (U := log x)).comp hlog ?_
    intro t ht
    constructor
    · exact log_le_log (by positivity : (0 : ℝ) < 2) ht.1
    · have hxpos : 0 < x := by linarith
      exact log_le_log (by linarith [ht.1]) ht.2
  have hstyle_div :
      ContinuousOn
        (fun t : ℝ ↦ Ramanujan.FKS14Calculations.styleVal (log t) / log t ^ (7 : ℕ))
        (Set.Icc 2 x) := by
    refine hstyle_log.div (ContinuousOn.pow hlog 7) ?_
    intro t ht
    exact pow_ne_zero _ (ne_of_gt (log_pos (by linarith [ht.1])))
  have hstyle_int :
      IntegrableOn
        (fun t : ℝ ↦ Ramanujan.FKS14Calculations.styleVal (log t) / log t ^ (7 : ℕ))
        (Set.Icc 2 x) volume :=
    ContinuousOn.integrableOn_Icc hstyle_div
  refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 hstyle_int
  intro t ht
  have ht1 : (1 : ℝ) < t := by
    linarith [ht.1]
  unfold a
  exact congrArg (fun u : ℝ => u / log t ^ (7 : ℕ))
    (Ramanujan.FKS14Calculations.formula_eq_style t ht1)

private theorem a_nonneg
    {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ a x :=
  Ramanujan.FKS14Calculations.a_nonneg_of
    (a := a)
    (ha_eq_admissible_ge_two := by
      intro z hz
      exact a_eq_admissible_ge_two hz)
    hx

private theorem a_mono :
    AntitoneOn a (Set.Ici xₐ) := by
  have hmono :
      AntitoneOn a (Set.Ici (exp (236 : ℝ))) :=
    Ramanujan.FKS14Calculations.a_mono_of
      (a := a)
      (ha_eq_admissible_ge_two := by
        intro z hz
        exact a_eq_admissible_ge_two hz)
  intro x hx y hy hxy
  have hx236 : exp (236 : ℝ) ≤ x := by
    have : exp (236 : ℝ) ≤ xₐ := by
      unfold xₐ
      exact exp_le_exp.mpr (by norm_num)
    exact le_trans this hx
  have hy236 : exp (236 : ℝ) ≤ y := by
    exact le_trans hx236 hxy
  exact hmono (Set.mem_Ici.mpr hx236) (Set.mem_Ici.mpr hy236) hxy

private theorem a_xa_upper :
    a xₐ ≤ (2793000000 : ℝ) := by
  simpa [xₐ] using
    (Ramanujan.FKS14Calculations.a_792_upper_of
      (a := a)
      (ha_eq_admissible_ge_two := by
        intro z hz
        exact a_eq_admissible_ge_two hz))

private theorem a_exa_upper :
    a exₐ ≤ (2774000000 : ℝ) := by
  simpa [exₐ] using
    (Ramanujan.FKS14Calculations.a_793_upper_of
      (a := a)
      (ha_eq_admissible_ge_two := by
        intro z hz
        exact a_eq_admissible_ge_two hz))

private theorem C₁_nonneg : 0 ≤ C₁ := by
  unfold C₁
  refine mul_nonneg ?_ ?_
  · exact div_nonneg (pow_nonneg log_xₐ_pos.le 6) xₐ_pos.le
  · apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    have ha : 0 ≤ a t := a_nonneg ht.1
    have hlog : 0 ≤ log t := log_nonneg (by linarith [ht.1])
    exact div_nonneg (by linarith) (pow_nonneg hlog 7)

private theorem C₁_le_large :
    C₁ ≤ (5000000 : ℝ) := by
  have ha_int :
      IntegrableOn (fun t ↦ a t / log t ^ (7 : ℕ)) (Set.Icc 2 xₐ) volume :=
    integrable_a_over_log7 xₐ two_le_xₐ
  have hJ770 :
      ∫ t in Set.Icc 2 (exp (770 : ℝ)), 1 / log t ^ (7 : ℕ)
        ≤ exp (770 : ℝ) / log (exp (770 : ℝ)) ^ (7 : ℕ)
          + 7 * (sqrt (exp (770 : ℝ)) / log 2 ^ (8 : ℕ)
            + 2 ^ (8 : ℕ) * exp (770 : ℝ) / log (exp (770 : ℝ)) ^ (8 : ℕ)) := by
    exact le_of_lt (Ramanujan.log_7_int_bound (exp (770 : ℝ)) two_le_exp_770)
  simpa [C₁, xₐ] using
    (Ramanujan.FKS14Calculations.C1_le_five_million_792_of
      (a := a)
      (xₐ := xₐ)
      (hxₐ := by rfl)
      (h2xa := two_le_xₐ)
      (ha_eq_admissible_ge_two := by
        intro z hz
        exact a_eq_admissible_ge_two hz)
      (ha_int := ha_int)
      (hJ770 := hJ770))

private theorem B_le_small :
    B ≤ (103 / 25000 : ℝ) := by
  simpa [B] using
    (Ramanujan.FKS14Calculations.B_le_small_792_of
      (xₐ := xₐ)
      (hxₐ := by rfl)
      (hlogxₐ := log_xₐ_val))

private theorem B_nonneg : 0 ≤ B := by
  unfold B
  rw [log_xₐ_val]
  positivity

set_option maxHeartbeats 1000000 in
-- This upper-bound proof reuses a long chain of Ramanujan helper inequalities and needs a larger heartbeat budget.
theorem pi_upper_specific :
    ∀ x > exₐ,
      pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
        + (Mₐ * x / log x ^ (6 : ℕ)) := by
  intro x hx
  have hxax : xₐ ≤ x := le_trans xₐ_le_exₐ (le_of_lt hx)
  have hx2 : 2 ≤ x := by
    linarith [two_le_exₐ]
  have htheta : ∀ t ≥ 2, |θ t - t| * log t ^ (5 : ℕ) ≤ t * a t := by
    intro t ht
    exact theta_bound t ht
  have ha_int :
      IntegrableOn (fun t ↦ a t / log t ^ (7 : ℕ)) (Set.Icc 2 x) volume :=
    integrable_a_over_log7 x hx2
  have hpi0 :
      pi x ≤ x / log x + a x * x / log x ^ (6 : ℕ) + (∫ t in Set.Icc 2 x, 1 / log t ^ (2 : ℕ))
        + ∫ t in Set.Icc 2 x, a t / log t ^ (7 : ℕ) :=
    Ramanujan.pi_upper a htheta x ha_int hx2
  have hI2 :
      ∫ t in Set.Icc 2 x, 1 / log t ^ (2 : ℕ) =
        x / log x ^ (2 : ℕ) + 2 * x / log x ^ (3 : ℕ) + 6 * x / log x ^ (4 : ℕ)
          + 24 * x / log x ^ (5 : ℕ) + 120 * x / log x ^ (6 : ℕ)
          - 2 * (∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1))
          + 720 * ∫ t in Set.Icc 2 x, 1 / log t ^ (7 : ℕ) :=
    Ramanujan.log_2_expansion_t x hx2
  have hsumx :
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) =
        x / log x + x / log x ^ (2 : ℕ) + 2 * x / log x ^ (3 : ℕ)
          + 6 * x / log x ^ (4 : ℕ) + 24 * x / log x ^ (5 : ℕ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
    ring
  have hS_nonneg : 0 ≤ (∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)) := by
    refine Finset.sum_nonneg ?_
    intro k hk
    exact div_nonneg (by positivity) (pow_nonneg (log_nonneg (by norm_num)) _)
  have hax_le : a x ≤ a exₐ :=
    a_mono (Set.mem_Ici.mpr xₐ_le_exₐ) (Set.mem_Ici.mpr hxax) (le_of_lt hx)
  have h720Ia :
      (720 : ℝ) * (∫ t in Set.Icc 2 x, 1 / log t ^ (7 : ℕ))
        + (∫ t in Set.Icc 2 x, a t / log t ^ (7 : ℕ))
        = ∫ t in Set.Icc 2 x, (720 + a t) / log t ^ (7 : ℕ) :=
    pi_upper_specific_h720Ia x ha_int
  have hG_int :
      IntegrableOn (fun t : ℝ ↦ (720 + a t) / log t ^ (7 : ℕ)) (Set.Icc 2 x) volume := by
    have h720_int :
        IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ (7 : ℕ)) (Set.Icc 2 x) volume := by
      have hJ_int :
          IntegrableOn (fun t : ℝ ↦ 1 / log t ^ (7 : ℕ)) (Set.Icc 2 x) volume :=
        ContinuousOn.integrableOn_Icc (continuousOn_const.div
          (ContinuousOn.pow
            (continuousOn_log.mono <| by
              intro t ht
              exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) fun t ht ↦
              pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1])
      have htmp :
          IntegrableOn (fun t : ℝ ↦ (720 : ℝ) * (1 / log t ^ (7 : ℕ))) (Set.Icc 2 x) volume :=
        hJ_int.const_mul 720
      refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
      intro t ht
      ring
    have h_add_int :
        IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ (7 : ℕ) + a t / log t ^ (7 : ℕ))
          (Set.Icc 2 x) volume :=
      h720_int.add ha_int
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 h_add_int
    intro t ht
    ring
  have hsplitG :
      ∫ t in Set.Icc 2 x, (720 + a t) / log t ^ (7 : ℕ) =
        (∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ (7 : ℕ))
          + (∫ t in Set.Icc xₐ x, (720 + a t) / log t ^ (7 : ℕ)) :=
    integral_Icc_split_at_xa (fun t ↦ (720 + a t) / log t ^ (7 : ℕ)) x hxax hG_int
  have htail_le :
      ∫ t in Set.Icc xₐ x, (720 + a t) / log t ^ (7 : ℕ) ≤
        (720 + a xₐ) * ∫ t in Set.Icc xₐ x, 1 / log t ^ (7 : ℕ) := by
    have htail_int :
        IntegrableOn (fun t : ℝ ↦ (720 + a t) / log t ^ (7 : ℕ)) (Set.Icc xₐ x) volume :=
      hG_int.mono_set (by
        intro t ht
        exact ⟨by linarith [two_le_xₐ, ht.1], ht.2⟩)
    have hconst_int :
        IntegrableOn (fun t : ℝ ↦ (720 + a xₐ) / log t ^ (7 : ℕ)) (Set.Icc xₐ x) volume :=
      ContinuousOn.integrableOn_Icc (continuousOn_const.div
        (ContinuousOn.pow
          (continuousOn_log.mono <| by
            intro t ht
            exact ne_of_gt (lt_of_lt_of_le (by linarith [two_le_xₐ]) ht.1)) _)
        fun t ht ↦
          pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [two_le_xₐ, ht.1])
    have hpt : ∀ t ∈ Set.Icc xₐ x, (720 + a t) / log t ^ (7 : ℕ) ≤ (720 + a xₐ) / log t ^ (7 : ℕ) := by
      intro t ht
      have hat : a t ≤ a xₐ :=
        a_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht.1) ht.1
      have hden_nonneg : 0 ≤ log t ^ (7 : ℕ) :=
        pow_nonneg (log_nonneg (by linarith [two_le_xₐ, ht.1])) 7
      have hnum : 720 + a t ≤ 720 + a xₐ := by
        linarith
      exact div_le_div_of_nonneg_right hnum hden_nonneg
    have := MeasureTheory.setIntegral_mono_on htail_int hconst_int measurableSet_Icc hpt
    have hconst_factor :
        ∫ t in Set.Icc xₐ x, (720 + a xₐ) / log t ^ (7 : ℕ) =
          (720 + a xₐ) * ∫ t in Set.Icc xₐ x, 1 / log t ^ (7 : ℕ) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
      intro t ht
      ring
    simpa [hconst_factor] using this
  have hJtail_le :
      ∫ t in Set.Icc xₐ x, 1 / log t ^ (7 : ℕ) ≤ ∫ t in Set.Icc 2 x, 1 / log t ^ (7 : ℕ) := by
    refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
    · have hJ_int :
          IntegrableOn (fun t : ℝ ↦ 1 / log t ^ (7 : ℕ)) (Set.Icc 2 x) volume :=
        ContinuousOn.integrableOn_Icc (continuousOn_const.div
          (ContinuousOn.pow
            (continuousOn_log.mono <| by
              intro t ht
              exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) fun t ht ↦
              pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1])
      exact hJ_int
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
      exact one_div_nonneg.mpr (pow_nonneg (log_nonneg (by linarith [ht.1])) _)
    · exact MeasureTheory.ae_of_all _ (fun t ht ↦ ⟨by linarith [ht.1, two_le_xₐ], ht.2⟩)
  have h720axa_nonneg : 0 ≤ 720 + a xₐ := by
    have haxa_nonneg : 0 ≤ a xₐ := a_nonneg two_le_xₐ
    linarith
  have h720axa_pos : 0 < 720 + a xₐ := by
    have haxa_nonneg : 0 ≤ a xₐ := a_nonneg two_le_xₐ
    linarith
  have hJfull_lt :
      ∫ t in Set.Icc 2 x, 1 / log t ^ (7 : ℕ) <
        x / log x ^ (7 : ℕ)
          + 7 * (sqrt x / log 2 ^ (8 : ℕ) + 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ)) :=
    Ramanujan.log_7_int_bound x hx2
  have htail_lt :
      ∫ t in Set.Icc xₐ x, (720 + a t) / log t ^ (7 : ℕ) <
        (720 + a xₐ) *
          (x / log x ^ (7 : ℕ)
            + 7 * (sqrt x / log 2 ^ (8 : ℕ) + 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ))) := by
    have hJtail_lt :
        ∫ t in Set.Icc xₐ x, 1 / log t ^ (7 : ℕ) <
          x / log x ^ (7 : ℕ)
            + 7 * (sqrt x / log 2 ^ (8 : ℕ) + 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ)) :=
      lt_of_le_of_lt hJtail_le hJfull_lt
    have hm :
        (720 + a xₐ) * ∫ t in Set.Icc xₐ x, 1 / log t ^ (7 : ℕ) <
          (720 + a xₐ) *
            (x / log x ^ (7 : ℕ)
              + 7 * (sqrt x / log 2 ^ (8 : ℕ) + 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ))) :=
      mul_lt_mul_of_pos_left hJtail_lt h720axa_pos
    exact lt_of_le_of_lt htail_le (by simpa [mul_assoc, mul_left_comm, mul_comm] using hm)
  have hlogxpos : 0 < log x := log_pos (by linarith [two_le_exₐ, hx])
  have hterm1 :
      x / log x ^ (7 : ℕ) ≤ x / log x ^ (6 : ℕ) * (1 / log xₐ) := by
    have hlog_le : log xₐ ≤ log x := log_le_log xₐ_pos hxax
    have hinv_log : (log x)⁻¹ ≤ (log xₐ)⁻¹ := inv_anti₀ log_xₐ_pos hlog_le
    have : (1 / log x) ≤ (1 / log xₐ) := by
      simpa [one_div] using hinv_log
    calc
      x / log x ^ (7 : ℕ) = (x / log x ^ (6 : ℕ)) * (1 / log x) := by
        field_simp [hlogxpos.ne']
      _ ≤ (x / log x ^ (6 : ℕ)) * (1 / log xₐ) := by
        gcongr
  have hterm2 :
      2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ) ≤
        x / log x ^ (6 : ℕ) * (2 ^ (8 : ℕ) / log xₐ ^ (2 : ℕ)) := by
    have hlog_le : log xₐ ≤ log x := log_le_log xₐ_pos hxax
    have hinv_log : (log x)⁻¹ ≤ (log xₐ)⁻¹ := inv_anti₀ log_xₐ_pos hlog_le
    have hinv_log' : 1 / log x ≤ 1 / log xₐ := by
      simpa [one_div] using hinv_log
    have hpow2 : (log x)⁻¹ ^ (2 : ℕ) ≤ (log xₐ)⁻¹ ^ (2 : ℕ) := by
      simpa [one_div] using
        (pow_le_pow_left₀ (one_div_nonneg.mpr (le_of_lt hlogxpos)) hinv_log' 2)
    have : 2 ^ (8 : ℕ) / log x ^ (2 : ℕ) ≤ 2 ^ (8 : ℕ) / log xₐ ^ (2 : ℕ) := by
      simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hpow2 (by positivity : 0 ≤ (2 ^ (8 : ℕ) : ℝ)))
    calc
      2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ) =
          (x / log x ^ (6 : ℕ)) * (2 ^ (8 : ℕ) / log x ^ (2 : ℕ)) := by
        field_simp [hlogxpos.ne']
      _ ≤ (x / log x ^ (6 : ℕ)) * (2 ^ (8 : ℕ) / log xₐ ^ (2 : ℕ)) := by
        gcongr
  have hterm3 :
      sqrt x / log 2 ^ (8 : ℕ) ≤
        x / log x ^ (6 : ℕ) * (log xₐ ^ (6 : ℕ) / (sqrt xₐ * log 2 ^ (8 : ℕ))) :=
    sqrt_term_bound_xa x hxax
  have hB :
      x / log x ^ (7 : ℕ) + 7 * (sqrt x / log 2 ^ (8 : ℕ) + 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ))
        ≤ x / log x ^ (6 : ℕ) * B := by
    have hterm2' :
        7 * 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ) ≤
          x / log x ^ (6 : ℕ) * (7 * 2 ^ (8 : ℕ) / log xₐ ^ (2 : ℕ)) := by
      have hmul := mul_le_mul_of_nonneg_left hterm2 (by positivity : 0 ≤ (7 : ℝ))
      ring_nf at hmul ⊢
      exact hmul
    have hsum_all :
        x / log x ^ (7 : ℕ) + 7 * (sqrt x / log 2 ^ (8 : ℕ) + 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ))
          ≤ x / log x ^ (7 : ℕ)
            + 7 *
              (x / log x ^ (6 : ℕ) * (log xₐ ^ (6 : ℕ) / (sqrt xₐ * log 2 ^ (8 : ℕ)))
                + 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ)) := by
      gcongr
    calc
      x / log x ^ (7 : ℕ) + 7 * (sqrt x / log 2 ^ (8 : ℕ) + 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ))
        ≤ x / log x ^ (7 : ℕ)
            + 7 *
              (x / log x ^ (6 : ℕ) * (log xₐ ^ (6 : ℕ) / (sqrt xₐ * log 2 ^ (8 : ℕ)))
                + 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ)) := hsum_all
      _ = (x / log x ^ (7 : ℕ) + 7 * 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ))
            + x / log x ^ (6 : ℕ) * (7 * log xₐ ^ (6 : ℕ) / (sqrt xₐ * log 2 ^ (8 : ℕ))) := by
        ring
      _ ≤ x / log x ^ (6 : ℕ) * (1 / log xₐ + 7 * 2 ^ (8 : ℕ) / log xₐ ^ (2 : ℕ))
            + x / log x ^ (6 : ℕ) * (7 * log xₐ ^ (6 : ℕ) / (sqrt xₐ * log 2 ^ (8 : ℕ))) := by
        have hsum12 :
            x / log x ^ (7 : ℕ) + 7 * 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ) ≤
              x / log x ^ (6 : ℕ) * (1 / log xₐ + 7 * 2 ^ (8 : ℕ) / log xₐ ^ (2 : ℕ)) := by
          nlinarith
        gcongr
      _ = x / log x ^ (6 : ℕ) * B := by
        unfold B
        ring
  have htail_B_lt :
      ∫ t in Set.Icc xₐ x, (720 + a t) / log t ^ (7 : ℕ) <
        (720 + a xₐ) * (x / log x ^ (6 : ℕ) * B) := by
    have htmp :
        (720 + a xₐ) *
            (x / log x ^ (7 : ℕ)
              + 7 * (sqrt x / log 2 ^ (8 : ℕ) + 2 ^ (8 : ℕ) * x / log x ^ (8 : ℕ)))
          ≤ (720 + a xₐ) * (x / log x ^ (6 : ℕ) * B) :=
      mul_le_mul_of_nonneg_left hB h720axa_nonneg
    exact lt_of_lt_of_le htail_lt htmp
  have hI0_eq :
      ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ (7 : ℕ) = C₁ * xₐ / log xₐ ^ (6 : ℕ) := by
    have htmp : C₁ = log xₐ ^ (6 : ℕ) / xₐ *
        ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ (7 : ℕ) := rfl
    have htmp2 :
        C₁ * xₐ / log xₐ ^ (6 : ℕ) =
          ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ (7 : ℕ) := by
      rw [htmp]
      field_simp [xₐ_pos.ne', log_xₐ_pos.ne']
    exact htmp2.symm
  have hG_lt :
      ∫ t in Set.Icc 2 x, (720 + a t) / log t ^ (7 : ℕ) <
        C₁ * x / log x ^ (6 : ℕ) + (720 + a xₐ) * (x / log x ^ (6 : ℕ) * B) := by
    rw [hsplitG]
    have hleft :
        ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ (7 : ℕ) ≤ C₁ * x / log x ^ (6 : ℕ) := by
      rw [hI0_eq]
      have hratio6 : xₐ / log xₐ ^ (6 : ℕ) ≤ x / log x ^ (6 : ℕ) := ratio6_bound_xa x hxax
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hratio6 C₁_nonneg)
    exact add_lt_add_of_le_of_lt hleft htail_B_lt
  have hmain_le :
      pi x ≤ x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
        + ((120 + a exₐ) * x / log x ^ (6 : ℕ))
        + (∫ t in Set.Icc 2 x, (720 + a t) / log t ^ (7 : ℕ)) :=
    pi_upper_specific_main_le x hx2 hpi0 hI2 hsumx hS_nonneg hax_le h720Ia
  have hM_bound :
      (120 + a exₐ) * x / log x ^ (6 : ℕ)
        + (C₁ * x / log x ^ (6 : ℕ) + (720 + a xₐ) * (x / log x ^ (6 : ℕ) * B))
      ≤ Mₐ * x / log x ^ (6 : ℕ) := by
    have hxlog6_nonneg : 0 ≤ x / log x ^ (6 : ℕ) :=
      div_nonneg (by linarith) (pow_nonneg (log_nonneg (by linarith)) 6)
    have hcoef :
        120 + a exₐ + C₁ + (720 + a xₐ) * B ≤ Mₐ := by
      have hax0 : 0 ≤ a xₐ := a_nonneg two_le_xₐ
      have htmp :
          120 + a exₐ + C₁ + (720 + a xₐ) * B ≤ (2800000000 : ℝ) := by
        have hBterm :
            (720 + a xₐ) * B ≤ (2793000720 : ℝ) * ((103 : ℝ) / 25000) := by
          have hsum : 720 + a xₐ ≤ (2793000720 : ℝ) := by
            linarith [hax0, a_xa_upper]
          exact le_trans
            (mul_le_mul_of_nonneg_right hsum B_nonneg)
            (mul_le_mul_of_nonneg_left B_le_small (by positivity : 0 ≤ (2793000720 : ℝ)))
        nlinarith [a_exa_upper, C₁_le_large, hBterm]
      simpa [Mₐ] using htmp
    have hmul :
        (120 + a exₐ + C₁ + (720 + a xₐ) * B) * (x / log x ^ (6 : ℕ))
          ≤ Mₐ * (x / log x ^ (6 : ℕ)) :=
      mul_le_mul_of_nonneg_right hcoef hxlog6_nonneg
    have hleft :
        (120 + a exₐ) * x / log x ^ (6 : ℕ)
          + (C₁ * x / log x ^ (6 : ℕ) + (720 + a xₐ) * (x / log x ^ (6 : ℕ) * B))
        = (120 + a exₐ + C₁ + (720 + a xₐ) * B) * (x / log x ^ (6 : ℕ)) := by
      ring
    have hright : Mₐ * (x / log x ^ (6 : ℕ)) = Mₐ * x / log x ^ (6 : ℕ) := by
      ring
    calc
      (120 + a exₐ) * x / log x ^ (6 : ℕ)
          + (C₁ * x / log x ^ (6 : ℕ) + (720 + a xₐ) * (x / log x ^ (6 : ℕ) * B))
        = (120 + a exₐ + C₁ + (720 + a xₐ) * B) * (x / log x ^ (6 : ℕ)) := hleft
      _ ≤ Mₐ * (x / log x ^ (6 : ℕ)) := hmul
      _ = Mₐ * x / log x ^ (6 : ℕ) := hright
  calc
    pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
      + ((120 + a exₐ) * x / log x ^ (6 : ℕ)
      + (C₁ * x / log x ^ (6 : ℕ) + (720 + a xₐ) * (x / log x ^ (6 : ℕ) * B))) := by
      have hmain_lt :
          x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
            + ((120 + a exₐ) * x / log x ^ (6 : ℕ))
            + (∫ t in Set.Icc 2 x, (720 + a t) / log t ^ (7 : ℕ))
          < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
            + ((120 + a exₐ) * x / log x ^ (6 : ℕ))
            + (C₁ * x / log x ^ (6 : ℕ) + (720 + a xₐ) * (x / log x ^ (6 : ℕ) * B)) := by
        gcongr
      linarith [hmain_le, hmain_lt]
    _ ≤ x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (Mₐ * x / log x ^ (6 : ℕ)) := by
      linarith [hM_bound]

theorem pi_lower_specific :
    ∀ x > xₐ,
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1))
        + (mₐ * x / log x ^ (6 : ℕ)) < pi x := by
  intro x hx
  have hlogx_gt : (792 : ℝ) < log x := by
    have hlog : log xₐ < log x := log_lt_log xₐ_pos hx
    simpa [xₐ, log_exp] using hlog
  have hlogx_pos : 0 < log x := by
    linarith
  have h4e9_le_xa : (4000000000 : ℝ) ≤ xₐ := by
    unfold xₐ
    have hexp23 : exp (23 : ℝ) < exp (792 : ℝ) := exp_lt_exp.mpr (by norm_num)
    linarith [Ramanujan.exp_23_gt_4e9, hexp23]
  have hx_ge_4e9 : x ≥ 4e9 := by
    linarith
  rcases Dusart.theorem_5_1 hx_ge_4e9 with ⟨E, hEeq, hEabs⟩
  have hsumx :
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) =
        x / log x + x / log x ^ (2 : ℕ) + 2 * x / log x ^ (3 : ℕ)
          + 6 * x / log x ^ (4 : ℕ) + 24 * x / log x ^ (5 : ℕ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
    ring
  have hmterm :
      (mₐ * x) / log x ^ (6 : ℕ) ≤ (5629000000 : ℝ) * x / log x ^ (6 : ℕ) := by
    have hxnonneg : 0 ≤ x := by linarith
    have hmconst : mₐ ≤ (5629000000 : ℝ) := by
      unfold mₐ
      norm_num
    have hmul :
        mₐ * x ≤ (5629000000 : ℝ) * x := mul_le_mul_of_nonneg_right hmconst hxnonneg
    exact div_le_div_of_nonneg_right hmul (pow_nonneg hlogx_pos.le 6)
  have htarget_le_m :
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (mₐ * x / log x ^ (6 : ℕ))
        ≤ x / log x *
          (1 + 1 / log x + 2 / log x ^ (2 : ℕ) + 6 / log x ^ (3 : ℕ)
            + 24 / log x ^ (4 : ℕ) + 5629000000 / log x ^ (5 : ℕ)) := by
    rw [hsumx]
    have halg :
        x / log x + x / log x ^ (2 : ℕ) + 2 * x / log x ^ (3 : ℕ)
            + 6 * x / log x ^ (4 : ℕ) + 24 * x / log x ^ (5 : ℕ)
            + (5629000000 : ℝ) * x / log x ^ (6 : ℕ)
          = x / log x *
              (1 + 1 / log x + 2 / log x ^ (2 : ℕ) + 6 / log x ^ (3 : ℕ)
                + 24 / log x ^ (4 : ℕ) + 5629000000 / log x ^ (5 : ℕ)) := by
      field_simp [hlogx_pos.ne']
    linarith
  have hlog792 :
      (3337 / 500 : ℝ) ≤ log (792 : ℝ) := by
    have haux : ∀ y ∈ Set.Icc (792 : ℝ) 792, (3337 / 500 : ℝ) ≤ log y := by
      interval_bound 20
    simpa using haux 792 ⟨le_rfl, le_rfl⟩
  have hpoly_pos :
      0 <
        2 * (log (log x) - 1) * log x ^ (3 : ℕ)
          - 13.32 * log x ^ (2 : ℕ) - 24 * log x - 5629000000 := by
    have hloglog_lb : (3337 / 500 : ℝ) < log (log x) := by
      have hloglog : log (792 : ℝ) < log (log x) := by
        exact log_lt_log (by positivity) hlogx_gt
      linarith
    have hcoef : (2837 / 250 : ℝ) ≤ 2 * (log (log x) - 1) := by
      nlinarith
    have hmain_lb :
        (2837 / 250 : ℝ) * log x ^ (3 : ℕ) ≤
          2 * (log (log x) - 1) * log x ^ (3 : ℕ) :=
      mul_le_mul_of_nonneg_right hcoef (pow_nonneg hlogx_pos.le 3)
    have hlogx_ge : (792 : ℝ) ≤ log x := le_of_lt hlogx_gt
    have hbase :
        0 <
          (2837 / 250 : ℝ) * (792 : ℝ) ^ (3 : ℕ)
            - 13.32 * (792 : ℝ) ^ (2 : ℕ) - 24 * (792 : ℝ) - 5629000000 := by
      norm_num
    have hquad_nonneg :
        0 ≤
          (2837 / 250 : ℝ) * (log x ^ (2 : ℕ) + (792 : ℝ) * log x + (792 : ℝ) ^ (2 : ℕ))
            - 13.32 * (log x + (792 : ℝ)) - 24 := by
      nlinarith
    have hdiff_nonneg :
        0 ≤
          ((2837 / 250 : ℝ) * log x ^ (3 : ℕ) - 13.32 * log x ^ (2 : ℕ) - 24 * log x - 5629000000)
            - ((2837 / 250 : ℝ) * (792 : ℝ) ^ (3 : ℕ)
              - 13.32 * (792 : ℝ) ^ (2 : ℕ) - 24 * (792 : ℝ) - 5629000000) := by
      have hfac :
          ((2837 / 250 : ℝ) * log x ^ (3 : ℕ) - 13.32 * log x ^ (2 : ℕ) - 24 * log x - 5629000000)
            - ((2837 / 250 : ℝ) * (792 : ℝ) ^ (3 : ℕ)
              - 13.32 * (792 : ℝ) ^ (2 : ℕ) - 24 * (792 : ℝ) - 5629000000)
            = (log x - (792 : ℝ)) *
                ((2837 / 250 : ℝ) *
                    (log x ^ (2 : ℕ) + (792 : ℝ) * log x + (792 : ℝ) ^ (2 : ℕ))
                  - 13.32 * (log x + (792 : ℝ)) - 24) := by
        ring
      rw [hfac]
      exact mul_nonneg (sub_nonneg.mpr hlogx_ge) hquad_nonneg
    have hpoly_aux :
        0 <
          (2837 / 250 : ℝ) * log x ^ (3 : ℕ)
            - 13.32 * log x ^ (2 : ℕ) - 24 * log x - 5629000000 := by
      linarith
    nlinarith [hmain_lb, hpoly_aux]
  have hinside_m :
      1 + 1 / log x + 2 / log x ^ (2 : ℕ) + 6 / log x ^ (3 : ℕ)
          + 24 / log x ^ (4 : ℕ) + 5629000000 / log x ^ (5 : ℕ)
        < 1 + 1 / log x + 2 * log (log x) / log x ^ (2 : ℕ) - 7.32 / log x ^ (3 : ℕ) := by
    have hdiff :
        (1 + 1 / log x + 2 * log (log x) / log x ^ (2 : ℕ) - 7.32 / log x ^ (3 : ℕ))
            - (1 + 1 / log x + 2 / log x ^ (2 : ℕ) + 6 / log x ^ (3 : ℕ)
              + 24 / log x ^ (4 : ℕ) + 5629000000 / log x ^ (5 : ℕ))
          = (2 * (log (log x) - 1) * log x ^ (3 : ℕ)
              - 13.32 * log x ^ (2 : ℕ) - 24 * log x - 5629000000) / log x ^ (5 : ℕ) := by
      field_simp [hlogx_pos.ne']
      ring
    have hdiff_pos :
        0 <
          (1 + 1 / log x + 2 * log (log x) / log x ^ (2 : ℕ) - 7.32 / log x ^ (3 : ℕ))
            - (1 + 1 / log x + 2 / log x ^ (2 : ℕ) + 6 / log x ^ (3 : ℕ)
              + 24 / log x ^ (4 : ℕ) + 5629000000 / log x ^ (5 : ℕ)) := by
      convert div_pos hpoly_pos (pow_pos hlogx_pos 5)
    nlinarith
  have htarget_lt_dusart :
      x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (mₐ * x / log x ^ (6 : ℕ))
        < x / log x * (1 + 1 / log x + 2 * log (log x) / log x ^ (2 : ℕ) - 7.32 / log x ^ (3 : ℕ)) := by
    have :
        x / log x *
            (1 + 1 / log x + 2 / log x ^ (2 : ℕ) + 6 / log x ^ (3 : ℕ)
              + 24 / log x ^ (4 : ℕ) + 5629000000 / log x ^ (5 : ℕ))
          < x / log x *
              (1 + 1 / log x + 2 * log (log x) / log x ^ (2 : ℕ) - 7.32 / log x ^ (3 : ℕ)) :=
      mul_lt_mul_of_pos_left hinside_m (by positivity)
    exact lt_of_le_of_lt htarget_le_m this
  have hEge : -(7.32 / log x ^ (3 : ℕ)) ≤ E := (abs_le.mp hEabs).1
  have hdusart_lower :
      x / log x * (1 + 1 / log x + 2 * log (log x) / log x ^ (2 : ℕ) - 7.32 / log x ^ (3 : ℕ))
        ≤ pi x := by
    have :
        x / log x * (1 + 1 / log x + 2 * log (log x) / log x ^ (2 : ℕ) - 7.32 / log x ^ (3 : ℕ))
          ≤ x / log x * (1 + 1 / log x + 2 * log (log x) / log x ^ (2 : ℕ) + E) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have : x / log x * (1 + 1 / log x + 2 * log (log x) / log x ^ (2 : ℕ) + E) = pi x := by
      simpa using hEeq.symm
    linarith
  exact lt_of_lt_of_le htarget_lt_dusart hdusart_lower

theorem epsilon_bound :
    ∀ x > exₐ, Ramanujan.ε Mₐ x - Ramanujan.εlower mₐ xₐ x < log x := by
  intro x hx
  have hlog_gt : (793 : ℝ) < log x := by
    have hlog : log exₐ < log x := log_lt_log exₐ_pos hx
    simpa [exₐ, log_exp] using hlog
  have hterm1 :
      (2 * Mₐ + 132) / log x ≤ (2 * (2800000000 : ℝ) + 132) / (793 : ℝ) := by
    have h1 :
        (2 * Mₐ + 132) / log x ≤ (2 * Mₐ + 132) / (793 : ℝ) :=
      div_le_div_of_nonneg_left (by nlinarith [show (0 : ℝ) ≤ Mₐ by simp [Mₐ]]) (by positivity)
        (le_of_lt hlog_gt)
    have h2 :
        (2 * Mₐ + 132) / (793 : ℝ) ≤ (2 * (2800000000 : ℝ) + 132) / (793 : ℝ) := by
      have : Mₐ ≤ (2800000000 : ℝ) := by simp [Mₐ]
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    exact le_trans h1 h2
  have hterm2 :
      (4 * Mₐ + 288) / log x ^ (2 : ℕ) ≤
        (4 * (2800000000 : ℝ) + 288) / (793 : ℝ) ^ (2 : ℕ) := by
    have h1 :
        (4 * Mₐ + 288) / log x ^ (2 : ℕ) ≤ (4 * Mₐ + 288) / (793 : ℝ) ^ (2 : ℕ) :=
      div_le_div_of_nonneg_left (by nlinarith [show (0 : ℝ) ≤ Mₐ by simp [Mₐ]]) (by positivity)
        (by
          have : (793 : ℝ) ^ (2 : ℕ) ≤ log x ^ (2 : ℕ) := by
            exact pow_le_pow_left₀ (by positivity) (le_of_lt hlog_gt) 2
          simpa using this)
    have h2 :
        (4 * Mₐ + 288) / (793 : ℝ) ^ (2 : ℕ) ≤
          (4 * (2800000000 : ℝ) + 288) / (793 : ℝ) ^ (2 : ℕ) := by
      have : Mₐ ≤ (2800000000 : ℝ) := by simp [Mₐ]
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    exact le_trans h1 h2
  have hterm3 :
      (12 * Mₐ + 576) / log x ^ (3 : ℕ) ≤
        (12 * (2800000000 : ℝ) + 576) / (793 : ℝ) ^ (3 : ℕ) := by
    have h1 :
        (12 * Mₐ + 576) / log x ^ (3 : ℕ) ≤ (12 * Mₐ + 576) / (793 : ℝ) ^ (3 : ℕ) :=
      div_le_div_of_nonneg_left (by nlinarith [show (0 : ℝ) ≤ Mₐ by simp [Mₐ]]) (by positivity)
        (by
          have : (793 : ℝ) ^ (3 : ℕ) ≤ log x ^ (3 : ℕ) := by
            exact pow_le_pow_left₀ (by positivity) (le_of_lt hlog_gt) 3
          simpa using this)
    have h2 :
        (12 * Mₐ + 576) / (793 : ℝ) ^ (3 : ℕ) ≤
          (12 * (2800000000 : ℝ) + 576) / (793 : ℝ) ^ (3 : ℕ) := by
      have : Mₐ ≤ (2800000000 : ℝ) := by simp [Mₐ]
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    exact le_trans h1 h2
  have hterm4 :
      (48 * Mₐ) / log x ^ (4 : ℕ) ≤
        (48 * (2800000000 : ℝ)) / (793 : ℝ) ^ (4 : ℕ) := by
    have h1 :
        (48 * Mₐ) / log x ^ (4 : ℕ) ≤ (48 * Mₐ) / (793 : ℝ) ^ (4 : ℕ) :=
      div_le_div_of_nonneg_left (by nlinarith [show (0 : ℝ) ≤ Mₐ by simp [Mₐ]]) (by positivity)
        (by
          have : (793 : ℝ) ^ (4 : ℕ) ≤ log x ^ (4 : ℕ) := by
            exact pow_le_pow_left₀ (by positivity) (le_of_lt hlog_gt) 4
          simpa using this)
    have h2 :
        (48 * Mₐ) / (793 : ℝ) ^ (4 : ℕ) ≤
          (48 * (2800000000 : ℝ)) / (793 : ℝ) ^ (4 : ℕ) := by
      have : Mₐ ≤ (2800000000 : ℝ) := by simp [Mₐ]
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    exact le_trans h1 h2
  have hterm5 :
      Mₐ ^ (2 : ℕ) / log x ^ (5 : ℕ) ≤
        (2800000000 : ℝ) ^ (2 : ℕ) / (793 : ℝ) ^ (5 : ℕ) := by
    have h1 :
        Mₐ ^ (2 : ℕ) / log x ^ (5 : ℕ) ≤ Mₐ ^ (2 : ℕ) / (793 : ℝ) ^ (5 : ℕ) :=
      div_le_div_of_nonneg_left (sq_nonneg Mₐ) (by positivity)
        (by
          have : (793 : ℝ) ^ (5 : ℕ) ≤ log x ^ (5 : ℕ) := by
            exact pow_le_pow_left₀ (by positivity) (le_of_lt hlog_gt) 5
          simpa using this)
    have h2 :
        Mₐ ^ (2 : ℕ) / (793 : ℝ) ^ (5 : ℕ) ≤
          (2800000000 : ℝ) ^ (2 : ℕ) / (793 : ℝ) ^ (5 : ℕ) := by
      have : Mₐ ^ (2 : ℕ) ≤ (2800000000 : ℝ) ^ (2 : ℕ) := by
        simp [Mₐ]
      exact div_le_div_of_nonneg_right this (by positivity)
    exact le_trans h1 h2
  have hdrop1 : 0 ≤ 364 / log x := by positivity
  have hdrop2 : 0 ≤ 381 / log x ^ (2 : ℕ) := by positivity
  have hdrop3 : 0 ≤ 238 / log x ^ (3 : ℕ) := by positivity
  have hdrop4 : 0 ≤ 97 / log x ^ (4 : ℕ) := by positivity
  have hdrop5 : 0 ≤ 30 / log x ^ (5 : ℕ) := by positivity
  have hdrop6 : 0 ≤ 8 / log x ^ (6 : ℕ) := by positivity
  rw [Ramanujan.εlower, if_pos (by simp [mₐ])]
  have hrew :
      Ramanujan.ε (2800000000 : ℝ) x - Ramanujan.ε' (5629000000 : ℝ) x
        =
          72 + 2 * (2800000000 : ℝ)
            + (2 * (2800000000 : ℝ) + 132) / log x
            + (4 * (2800000000 : ℝ) + 288) / log x ^ (2 : ℕ)
            + (12 * (2800000000 : ℝ) + 576) / log x ^ (3 : ℕ)
            + (48 * (2800000000 : ℝ)) / log x ^ (4 : ℕ)
            + (2800000000 : ℝ) ^ (2 : ℕ) / log x ^ (5 : ℕ)
            - (206 + (5629000000 : ℝ))
            - (364 / log x + 381 / log x ^ (2 : ℕ) + 238 / log x ^ (3 : ℕ)
              + 97 / log x ^ (4 : ℕ) + 30 / log x ^ (5 : ℕ) + 8 / log x ^ (6 : ℕ)) := by
    unfold Ramanujan.ε Ramanujan.ε'
    ring
  have hdrop :
      Ramanujan.ε (2800000000 : ℝ) x - Ramanujan.ε' (5629000000 : ℝ) x
        ≤
          72 + 2 * (2800000000 : ℝ)
            + (2 * (2800000000 : ℝ) + 132) / log x
            + (4 * (2800000000 : ℝ) + 288) / log x ^ (2 : ℕ)
            + (12 * (2800000000 : ℝ) + 576) / log x ^ (3 : ℕ)
            + (48 * (2800000000 : ℝ)) / log x ^ (4 : ℕ)
            + (2800000000 : ℝ) ^ (2 : ℕ) / log x ^ (5 : ℕ)
            - (206 + (5629000000 : ℝ)) := by
    rw [hrew]
    nlinarith
  have hupper :
      Ramanujan.ε (2800000000 : ℝ) x - Ramanujan.ε' (5629000000 : ℝ) x
        ≤ 72 + 2 * (2800000000 : ℝ)
          + (2 * (2800000000 : ℝ) + 132) / (793 : ℝ)
          + (4 * (2800000000 : ℝ) + 288) / (793 : ℝ) ^ (2 : ℕ)
          + (12 * (2800000000 : ℝ) + 576) / (793 : ℝ) ^ (3 : ℕ)
          + (48 * (2800000000 : ℝ)) / (793 : ℝ) ^ (4 : ℕ)
          + (2800000000 : ℝ) ^ (2 : ℕ) / (793 : ℝ) ^ (5 : ℕ)
          - (206 + (5629000000 : ℝ)) := by
    have hterm1' :
        (2 * (2800000000 : ℝ) + 132) / log x ≤ (2 * (2800000000 : ℝ) + 132) / (793 : ℝ) := by
      simpa [Mₐ] using hterm1
    have hterm2' :
        (4 * (2800000000 : ℝ) + 288) / log x ^ (2 : ℕ) ≤
          (4 * (2800000000 : ℝ) + 288) / (793 : ℝ) ^ (2 : ℕ) := by
      simpa [Mₐ] using hterm2
    have hterm3' :
        (12 * (2800000000 : ℝ) + 576) / log x ^ (3 : ℕ) ≤
          (12 * (2800000000 : ℝ) + 576) / (793 : ℝ) ^ (3 : ℕ) := by
      simpa [Mₐ] using hterm3
    have hterm4' :
        (48 * (2800000000 : ℝ)) / log x ^ (4 : ℕ) ≤
          (48 * (2800000000 : ℝ)) / (793 : ℝ) ^ (4 : ℕ) := by
      simpa [Mₐ] using hterm4
    have hterm5' :
        (2800000000 : ℝ) ^ (2 : ℕ) / log x ^ (5 : ℕ) ≤
          (2800000000 : ℝ) ^ (2 : ℕ) / (793 : ℝ) ^ (5 : ℕ) := by
      simpa [Mₐ] using hterm5
    have hmono :
        72 + 2 * (2800000000 : ℝ)
          + (2 * (2800000000 : ℝ) + 132) / log x
          + (4 * (2800000000 : ℝ) + 288) / log x ^ (2 : ℕ)
          + (12 * (2800000000 : ℝ) + 576) / log x ^ (3 : ℕ)
          + (48 * (2800000000 : ℝ)) / log x ^ (4 : ℕ)
          + (2800000000 : ℝ) ^ (2 : ℕ) / log x ^ (5 : ℕ)
          - (206 + (5629000000 : ℝ))
        ≤ 72 + 2 * (2800000000 : ℝ)
          + (2 * (2800000000 : ℝ) + 132) / (793 : ℝ)
          + (4 * (2800000000 : ℝ) + 288) / (793 : ℝ) ^ (2 : ℕ)
          + (12 * (2800000000 : ℝ) + 576) / (793 : ℝ) ^ (3 : ℕ)
          + (48 * (2800000000 : ℝ)) / (793 : ℝ) ^ (4 : ℕ)
          + (2800000000 : ℝ) ^ (2 : ℕ) / (793 : ℝ) ^ (5 : ℕ)
          - (206 + (5629000000 : ℝ)) := by
      linarith [hterm1', hterm2', hterm3', hterm4', hterm5']
    exact le_trans hdrop hmono
  have hconst :
      72 + 2 * (2800000000 : ℝ)
        + (2 * (2800000000 : ℝ) + 132) / (793 : ℝ)
        + (4 * (2800000000 : ℝ) + 288) / (793 : ℝ) ^ (2 : ℕ)
        + (12 * (2800000000 : ℝ) + 576) / (793 : ℝ) ^ (3 : ℕ)
        + (48 * (2800000000 : ℝ)) / (793 : ℝ) ^ (4 : ℕ)
        + (2800000000 : ℝ) ^ (2 : ℕ) / (793 : ℝ) ^ (5 : ℕ)
        - (206 + (5629000000 : ℝ))
      < (793 : ℝ) := by
    norm_num
  exact lt_trans (lt_of_le_of_lt hupper hconst) hlog_gt

theorem ramanujan_final :
    ∀ x > exₐ, pi x ^ (2 : ℕ) < exp 1 * x / log x * pi (x / exp 1) :=
  by
    intro x hx
    have hupper :
        ∀ y > exp 1 * xₐ,
          pi y < y * ∑ k ∈ Finset.range 5, (k.factorial / log y ^ (k + 1))
            + (Mₐ * y / log y ^ (6 : ℕ)) := by
      intro y hy
      have hy' : y > exₐ := by
        simpa [exₐ_eq] using hy
      exact pi_upper_specific y hy'
    exact Ramanujan.criterion mₐ Mₐ xₐ exₐ
      one_lt_xₐ
      pi_lower_specific
      hupper
      exₐ_ge_e_xₐ
      epsilon_bound x hx

end RamanujanFKS14
