import krylov.Strings.Volterra
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
Article: main_krylov, apC:eq:state (finite-window construction).
Use: Remove the short-window restriction in the measure-driven Volterra
construction. Every finite positive mass, including arbitrary atoms and singular
continuous mass, admits a unique continuous displacement on every finite window.
Source: the classical exponentially weighted Volterra contraction argument;
Banach's fixed-point theorem and `Real.mul_exp_neg_le_exp_neg_one` in mathlib.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Window

/-- Exponential damping of the causal Green kernel. -/
def dampedKernel {L : ℝ≥0} (c : ℝ) (x y : Window L) : ℝ :=
  kernel x y * Real.exp (-c * kernel x y)

theorem dampedKernel_nonneg {L : ℝ≥0} (c : ℝ) (x y : Window L) :
    0 ≤ dampedKernel c x y :=
  mul_nonneg (kernel_nonneg x y) (Real.exp_nonneg _)

/-- The damped Green kernel is bounded independently of window length. -/
theorem dampedKernel_le {L : ℝ≥0} {c : ℝ} (hc : 0 < c) (x y : Window L) :
    dampedKernel c x y ≤ 1 / c := by
  have he := Real.mul_exp_neg_le_exp_neg_one (c * kernel x y)
  have he1 : Real.exp (-1) ≤ 1 := by norm_num
  apply (le_div_iff₀ hc).mpr
  dsimp [dampedKernel]
  have harg : -c * kernel x y = -(c * kernel x y) := by ring
  rw [harg]
  nlinarith

/-- Affine Picard map for the exponentially rescaled displacement. -/
def dampedPicard {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    (a b c : ℝ) (f : C(Window L, ℝ)) : C(Window L, ℝ) where
  toFun x := (a + b * (x : ℝ)) * Real.exp (-c * (x : ℝ)) +
    ∫ y, dampedKernel c x y * f y ∂ν
  continuous_toFun := by
    have hk : Continuous (fun z : Window L × Window L ↦ dampedKernel c z.1 z.2 * f z.2) := by
      unfold dampedKernel kernel
      fun_prop
    have hi := continuous_parametric_integral_of_continuous (μ := ν)
      (f := fun x y : Window L ↦ dampedKernel c x y * f y) hk isCompact_univ
    have hfree : Continuous (fun x : Window L ↦
        (a + b * (x : ℝ)) * Real.exp (-c * (x : ℝ))) := by fun_prop
    exact hfree.add (by simpa only [Measure.restrict_univ] using hi)

/-- The rescaled Picard map contracts as soon as its exponential weight exceeds
the mass, with no restriction on the physical length. -/
theorem dampedPicard_dist_le {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    (a b : ℝ) {c : ℝ} (hc : 0 < c) (f g : C(Window L, ℝ)) :
    dist (dampedPicard ν a b c f) (dampedPicard ν a b c g) ≤
      ((1 / c) * ν.real univ) * dist f g := by
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖((a + b * (x : ℝ)) * Real.exp (-c * (x : ℝ)) +
      ∫ y, dampedKernel c x y * f y ∂ν) -
    ((a + b * (x : ℝ)) * Real.exp (-c * (x : ℝ)) +
      ∫ y, dampedKernel c x y * g y ∂ν)‖ ≤ _
  rw [add_sub_add_left_eq_sub]
  have hfi : Integrable (fun y ↦ dampedKernel c x y * f y) ν := by
    apply Continuous.integrable_of_hasCompactSupport
    · unfold dampedKernel kernel
      fun_prop
    · exact HasCompactSupport.of_compactSpace _
  have hgi : Integrable (fun y ↦ dampedKernel c x y * g y) ν := by
    apply Continuous.integrable_of_hasCompactSupport
    · unfold dampedKernel kernel
      fun_prop
    · exact HasCompactSupport.of_compactSpace _
  rw [← integral_sub hfi hgi]
  calc
    _ ≤ ((1 / c) * ‖f - g‖) * ν.real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards with y
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (dampedKernel_nonneg c x y)]
      exact mul_le_mul (dampedKernel_le hc x y) ((f - g).norm_coe_le_norm y)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [dist_eq_norm]; ring

theorem dampedPicard_contracting {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    (a b : ℝ) {c : ℝ} (hc : 0 < c) (hm : ν.real univ < c) :
    ContractingWith ⟨(1 / c) * ν.real univ, by positivity⟩ (dampedPicard ν a b c) := by
  constructor
  · change (1 / c) * ν.real univ < 1
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hc]
    simpa using hm
  · apply LipschitzWith.of_dist_le_mul
    intro f g
    exact dampedPicard_dist_le ν a b hc f g

/-- Removing the exponential weight recovers the causal Green kernel exactly. -/
theorem unweight_kernel {L : ℝ≥0} (c : ℝ) (x y : Window L) :
    Real.exp (c * (x : ℝ)) * dampedKernel c x y =
      kernel x y * Real.exp (c * (y : ℝ)) := by
  by_cases hxy : (y : ℝ) ≤ x
  · have hk : kernel x y = (x : ℝ) - y := max_eq_left (sub_nonneg.mpr hxy)
    rw [dampedKernel, hk]
    calc
      _ = ((x : ℝ) - y) * (Real.exp (c * (x : ℝ)) *
          Real.exp (-c * ((x : ℝ) - y))) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  · have hk : kernel x y = 0 := max_eq_right (by linarith)
    simp [dampedKernel, hk]

/-- Exponential rescaling is an exact equivalence of the two fixed-point
equations; no approximation or limiting argument enters. -/
theorem unweight_fixedPoint {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    (a b c : ℝ) (g : C(Window L, ℝ))
    (hg : Function.IsFixedPt (dampedPicard ν a b c) g) :
    ∀ x : Window L, Real.exp (c * (x : ℝ)) * g x = a + b * (x : ℝ) +
      ∫ y, kernel x y * (Real.exp (c * (y : ℝ)) * g y) ∂ν := by
  intro x
  have hx := congrArg (fun h : C(Window L, ℝ) ↦ h x) hg
  change (a + b * (x : ℝ)) * Real.exp (-c * (x : ℝ)) +
    ∫ y, dampedKernel c x y * g y ∂ν = g x at hx
  rw [← hx, mul_add, ← integral_const_mul]
  have he : Real.exp (c * (x : ℝ)) * Real.exp (-c * (x : ℝ)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2; ring
  have hfirst : Real.exp (c * (x : ℝ)) *
      ((a + b * (x : ℝ)) * Real.exp (-c * (x : ℝ))) = a + b * (x : ℝ) := by
    calc
      _ = (a + b * (x : ℝ)) * (Real.exp (c * (x : ℝ)) *
          Real.exp (-c * (x : ℝ))) := by ring
      _ = _ := by rw [he, mul_one]
  rw [hfirst]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [← mul_assoc, unweight_kernel]
  ring

/-- On every finite window and for every finite positive mass there is a unique
continuous displacement solving the genuine Volterra equation. This includes
arbitrarily many atoms and singular continuous mass; no smallness is assumed. -/
theorem existsUnique_volterra_finite {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    (a b : ℝ) : ∃! f : C(Window L, ℝ), ∀ x,
      f x = a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν := by
  let c := ν.real univ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hm : ν.real univ < c := by dsimp [c]; linarith
  let hcon := dampedPicard_contracting ν a b hc hm
  let g := hcon.fixedPoint (dampedPicard ν a b c)
  let f : C(Window L, ℝ) := ⟨fun x ↦ Real.exp (c * (x : ℝ)) * g x, by fun_prop⟩
  have hf : ∀ x, f x = a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν :=
    unweight_fixedPoint ν a b c g hcon.fixedPoint_isFixedPt
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  let g' : C(Window L, ℝ) := ⟨fun x ↦ Real.exp (-c * (x : ℝ)) * f' x, by fun_prop⟩
  have hfg : ∀ x, f' x = Real.exp (c * (x : ℝ)) * g' x := by
    intro x
    change f' x = Real.exp (c * (x : ℝ)) * (Real.exp (-c * (x : ℝ)) * f' x)
    rw [← mul_assoc, ← Real.exp_add]
    have hz : c * (x : ℝ) + -c * (x : ℝ) = 0 := by ring
    rw [hz, Real.exp_zero, one_mul]
  have hg' : Function.IsFixedPt (dampedPicard ν a b c) g' := by
    ext x
    apply (mul_left_cancel₀ (Real.exp_ne_zero (c * (x : ℝ))))
    change Real.exp (c * (x : ℝ)) *
        ((a + b * (x : ℝ)) * Real.exp (-c * (x : ℝ)) +
          ∫ y, dampedKernel c x y * g' y ∂ν) = Real.exp (c * (x : ℝ)) * g' x
    rw [mul_add, ← integral_const_mul, ← hfg x]
    have he : Real.exp (c * (x : ℝ)) *
        ((a + b * (x : ℝ)) * Real.exp (-c * (x : ℝ))) = a + b * (x : ℝ) := by
      calc
        _ = (a + b * (x : ℝ)) * (Real.exp (c * (x : ℝ)) *
            Real.exp (-c * (x : ℝ))) := by ring
        _ = _ := by rw [← Real.exp_add]; simp
    rw [he, hf' x]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    rw [← mul_assoc, unweight_kernel, hfg y]
    ring
  have hgg : g' = g := hcon.fixedPoint_unique hg'
  ext x
  rw [hfg, hgg]
  rfl

/-- Nonnegative data produce a nonnegative displacement on every finite
window. Positivity is derived from the damped Picard iteration, not imposed
as an admissibility field. -/
theorem volterra_nonneg_finite {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {f : C(Window L, ℝ)}
    (hf : ∀ x, f x = a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν) :
    ∀ x, 0 ≤ f x := by
  let c := ν.real univ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hm : ν.real univ < c := by dsimp [c]; linarith
  let hcon := dampedPicard_contracting ν a b hc hm
  let g := hcon.fixedPoint (dampedPicard ν a b c)
  let fstar : C(Window L, ℝ) := ⟨fun x ↦ Real.exp (c * (x : ℝ)) * g x, by fun_prop⟩
  have hfstar : ∀ x, fstar x = a + b * (x : ℝ) + ∫ y, kernel x y * fstar y ∂ν :=
    unweight_fixedPoint ν a b c g hcon.fixedPoint_isFixedPt
  obtain ⟨f₀, _, hu⟩ := existsUnique_volterra_finite ν a b
  have heq : f = fstar := (hu f hf).trans (hu fstar hfstar).symm
  have hiter : ∀ n : ℕ, ∀ x : Window L, 0 ≤
      ((dampedPicard ν a b c)^[n] (0 : C(Window L, ℝ))) x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      change 0 ≤ (a + b * (x : ℝ)) * Real.exp (-c * (x : ℝ)) +
        ∫ y, dampedKernel c x y *
          ((dampedPicard ν a b c)^[n] (0 : C(Window L, ℝ))) y ∂ν
      apply add_nonneg
      · exact mul_nonneg (add_nonneg ha (mul_nonneg hb x.property.1)) (Real.exp_nonneg _)
      · exact integral_nonneg (fun y ↦ mul_nonneg (dampedKernel_nonneg c x y) (ih y))
  have hg : ∀ x, 0 ≤ g x := by
    intro x
    have ht := (continuous_eval_const x).tendsto g |>.comp
      (hcon.tendsto_iterate_fixedPoint (0 : C(Window L, ℝ)))
    exact ge_of_tendsto ht (Eventually.of_forall (fun n ↦ hiter n x))
  intro x
  rw [heq]
  exact mul_nonneg (Real.exp_nonneg _) (hg x)

/-- The full finite-window solution lies above free motion. -/
theorem volterra_ge_free_finite {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {f : C(Window L, ℝ)}
    (hf : ∀ x, f x = a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν)
    (x : Window L) : a + b * (x : ℝ) ≤ f x := by
  have hn := volterra_nonneg_finite ν ha hb hf
  rw [hf x]
  exact le_add_of_nonneg_right (integral_nonneg (fun y ↦ mul_nonneg (kernel_nonneg x y) (hn y)))

/-- The finite-window solution is monotone for nonnegative initial data. -/
theorem volterra_monotone_finite {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {f : C(Window L, ℝ)}
    (hf : ∀ x, f x = a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν) :
    Monotone f := by
  have hn := volterra_nonneg_finite ν ha hb hf
  intro x y hxy
  have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
  rw [hf x, hf y]
  apply add_le_add
  · gcongr
  · apply integral_mono
    · apply Continuous.integrable_of_hasCompactSupport
      · unfold kernel
        fun_prop
      · exact HasCompactSupport.of_compactSpace _
    · apply Continuous.integrable_of_hasCompactSupport
      · unfold kernel
        fun_prop
      · exact HasCompactSupport.of_compactSpace _
    · intro z
      exact mul_le_mul_of_nonneg_right (max_le_max (sub_le_sub_right hxy' _) le_rfl) (hn z)

end Window
end
end krylov.Strings
