import krylov.Strings.Mass
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
Article: main_krylov, apC:eq:state (local construction).
Use: Construct the string displacement by a genuine Volterra equation against
an arbitrary finite positive measure, including atomic and singular measures.
Source: Banach's contraction principle (`ContractingWith.fixedPoint`) and
mathlib's continuity theorem for parametric integrals on compact sets.

The small-window condition is explicit. Global continuation and equivalence
with the coupled first-order state equations are separate analytic steps.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- A compact physical window, represented as a compact topological space. -/
abbrev Window (L : ℝ≥0) := Icc (0 : ℝ) (L : ℝ)

namespace Window

/-- The positive-part Green kernel of the second-order string equation. -/
def kernel {L : ℝ≥0} (x y : Window L) : ℝ := max ((x : ℝ) - y) 0

theorem kernel_nonneg {L : ℝ≥0} (x y : Window L) : 0 ≤ kernel x y :=
  le_max_right _ _

theorem kernel_le {L : ℝ≥0} (x y : Window L) : kernel x y ≤ L := by
  apply max_le
  · exact sub_le_iff_le_add.mpr (x.property.2.trans (le_add_of_nonneg_right y.property.1))
  · exact L.property

/-- Free motion plus the actual measure-driven response. The continuity field
is proved by the compact parametric integral theorem, without a density.
-/
def picard {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    (a b : ℝ) (f : C(Window L, ℝ)) : C(Window L, ℝ) where
  toFun x := a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν
  continuous_toFun := by
    have hc : Continuous (fun z : Window L × Window L ↦ kernel z.1 z.2 * f z.2) := by
      unfold kernel
      fun_prop
    have hi := continuous_parametric_integral_of_continuous (μ := ν)
      (f := fun x y : Window L ↦ kernel x y * f y) hc isCompact_univ
    have hfree : Continuous (fun x : Window L ↦ a + b * (x : ℝ)) := by fun_prop
    exact hfree.add (by simpa only [Measure.restrict_univ] using hi)

/-- The Volterra operator has exactly the expected short-window Lipschitz
bound, proportional to length times mass. -/
theorem picard_dist_le {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    (a b : ℝ) (f g : C(Window L, ℝ)) :
    dist (picard ν a b f) (picard ν a b g) ≤
      ((L : ℝ) * ν.real univ) * dist f g := by
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  change ‖(a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν) -
    (a + b * (x : ℝ) + ∫ y, kernel x y * g y ∂ν)‖ ≤ _
  rw [add_sub_add_left_eq_sub]
  have hfi : Integrable (fun y ↦ kernel x y * f y) ν := by
    apply Continuous.integrable_of_hasCompactSupport
    · unfold kernel
      fun_prop
    · exact HasCompactSupport.of_compactSpace _
  have hgi : Integrable (fun y ↦ kernel x y * g y) ν := by
    apply Continuous.integrable_of_hasCompactSupport
    · unfold kernel
      fun_prop
    · exact HasCompactSupport.of_compactSpace _
  rw [← integral_sub hfi hgi]
  calc
    _ ≤ ((L : ℝ) * ‖f - g‖) * ν.real univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards with y
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (kernel_nonneg x y)]
      exact mul_le_mul (kernel_le x y) ((f - g).norm_coe_le_norm y)
        (norm_nonneg _) L.property
    _ = _ := by rw [dist_eq_norm]; ring

/-- A finite positive mass gives a genuine contracting Picard map whenever
window length times total mass is below one. -/
theorem picard_contracting {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    (a b : ℝ) (hsmall : (L : ℝ) * ν.real univ < 1) :
    ContractingWith ⟨(L : ℝ) * ν.real univ, by positivity⟩ (picard ν a b) := by
  constructor
  · exact hsmall
  · apply LipschitzWith.of_dist_le_mul
    intro f g
    exact picard_dist_le ν a b f g

/-- Local existence and uniqueness of the displacement Volterra equation for
arbitrary finite string mass. Neither absolute continuity nor a finite number
of atoms is assumed. -/
theorem existsUnique_volterra {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    (a b : ℝ) (hsmall : (L : ℝ) * ν.real univ < 1) :
    ∃! f : C(Window L, ℝ), ∀ x,
      f x = a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν := by
  let hc := picard_contracting ν a b hsmall
  refine ⟨hc.fixedPoint (picard ν a b), ?_, ?_⟩
  · intro x
    exact congrArg (fun f : C(Window L, ℝ) ↦ f x) hc.fixedPoint_isFixedPt |>.symm
  · intro f hf
    apply hc.fixedPoint_unique
    ext x
    exact (hf x).symm

/-- The boundary value of every solution is the prescribed displacement;
the kernel vanishes at the left endpoint, even in the presence of an atom. -/
theorem volterra_origin {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    (a b : ℝ) {f : C(Window L, ℝ)}
    (hf : ∀ x, f x = a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν) :
    f ⟨0, ⟨le_rfl, L.property⟩⟩ = a := by
  rw [hf]
  have hz (y : Window L) : kernel ⟨0, ⟨le_rfl, L.property⟩⟩ y = 0 := by
    dsimp [kernel]
    exact max_eq_right (by linarith [y.property.1])
  simp [hz]

/-- Positivity is preserved by Picard iteration against an arbitrary positive
measure. This is an order argument, not an assumption on the eventual state. -/
theorem picard_lower_bound {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    {a b : ℝ} (hb : 0 ≤ b) {f : C(Window L, ℝ)} (hf : ∀ x, 0 ≤ f x)
    (x : Window L) : a ≤ picard ν a b f x := by
  change a ≤ a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν
  have hi : 0 ≤ ∫ y, kernel x y * f y ∂ν := by
    apply integral_nonneg
    intro y
    exact mul_nonneg (kernel_nonneg x y) (hf y)
  linarith [mul_nonneg hb x.property.1]

/-- The actual local Volterra solution is nonnegative for nonnegative initial
position and slope. Proof: all Picard iterates are nonnegative and converge
uniformly by the contraction theorem. -/
theorem volterra_nonneg {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsmall : (L : ℝ) * ν.real univ < 1) {f : C(Window L, ℝ)}
    (hf : ∀ x, f x = a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν) :
    ∀ x, 0 ≤ f x := by
  let hc := picard_contracting ν a b hsmall
  have hfix : f = hc.fixedPoint (picard ν a b) := by
    apply hc.fixedPoint_unique
    ext x
    exact (hf x).symm
  have hiter : ∀ n : ℕ, ∀ x : Window L,
      0 ≤ ((picard ν a b)^[n] (ContinuousMap.const _ a)) x := by
    intro n
    induction n with
    | zero => simpa using fun _ : Window L ↦ ha
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      exact ha.trans (picard_lower_bound ν hb ih x)
  intro x
  have ht := (continuous_eval_const x).tendsto
    (hc.fixedPoint (picard ν a b)) |>.comp
      (hc.tendsto_iterate_fixedPoint (ContinuousMap.const _ a))
  rw [← hfix] at ht
  exact ge_of_tendsto ht (Eventually.of_forall (fun n ↦ hiter n x))

/-- A string with nonnegative initial data lies above its free trajectory.
For the normalized string this gives `φ(x) ≥ 1+x`, with atoms allowed. -/
theorem volterra_ge_free {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsmall : (L : ℝ) * ν.real univ < 1) {f : C(Window L, ℝ)}
    (hf : ∀ x, f x = a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν)
    (x : Window L) : a + b * (x : ℝ) ≤ f x := by
  have hn := volterra_nonneg ν ha hb hsmall hf
  rw [hf x]
  exact le_add_of_nonneg_right (integral_nonneg (fun y ↦ mul_nonneg (kernel_nonneg x y) (hn y)))

/-- Monotonicity of the actual Volterra solution follows from positivity of
the measure and the Green kernel, including across arbitrarily many atoms. -/
theorem volterra_monotone {L : ℝ≥0} (ν : Measure (Window L)) [IsFiniteMeasure ν]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsmall : (L : ℝ) * ν.real univ < 1) {f : C(Window L, ℝ)}
    (hf : ∀ x, f x = a + b * (x : ℝ) + ∫ y, kernel x y * f y ∂ν) :
    Monotone f := by
  have hn := volterra_nonneg ν ha hb hsmall hf
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
