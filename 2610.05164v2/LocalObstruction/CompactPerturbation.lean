import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Topology.Compactness.Compact

/-!
Article: 2610.05164v2, Theorem 6.1.
Compact smooth perturbations and the distributional step in Theorem 6.1.
Use: `«2610.05164v2».LocalObstruction.continuous_eq_zero_of_test_integrals` feeds
`«2610.05164v2».LocalObstruction.sine_nonstationary_test` (sine nonstationary test).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff

/--
Defines `perturb` of type `ℝ` by `m x+∑ i, a i*v i x`.

Use: `«2610.05164v2».LocalObstruction.finite_perturbation_positive` uses this definition to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ a : ι → ℝ in 𝓝 0,
∀ x, 0<perturb m v a x`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic`.
-/
def perturb {ι : Type*} [Fintype ι] (m : ℝ → ℝ) (v : ι → ℝ → ℝ)
    (a : ι → ℝ) (x : ℝ) : ℝ := m x+∑ i, a i*v i x

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ a : ι → ℝ in 𝓝 0, ∀ x,
0<perturb m v a x`.

Use: `«2610.05164v2».LocalObstruction.actual_ground_root_near` uses this bound to establish
establishes the stated eventual or almost-everywhere assertion `∀ᶠ a : ι → ℝ in 𝓝 0,
perturbTransmission hm hv (a,-groundCoupling (perturb m v a))=0`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic`.

Proof: Separate `x ∈ K` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem finite_perturbation_positive {ι : Type*} [Fintype ι]
    {m : ℝ → ℝ} {v : ι → ℝ → ℝ} (hm : Continuous m)
    (hpos : ∀ x, 0<m x) (hv : ∀ i, Continuous (v i))
    (hcompact : ∀ i, HasCompactSupport (v i)) :
    ∀ᶠ a : ι → ℝ in 𝓝 0, ∀ x, 0<perturb m v a x := by
  -- Separate `x ∈ K` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  let K : Set ℝ := ⋃ i, tsupport (v i)
  have hK : IsCompact K := isCompact_iUnion hcompact
  -- Establish continuity hF before using the function at limits or in calculus arguments.
  have hF : Continuous (fun z : (ι → ℝ) × ℝ => perturb m v z.1 z.2) := by
    unfold perturb
    apply (hm.comp continuous_snd).add
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_fst).mul ((hv i).comp continuous_snd)
  have hlocal : ∀ x ∈ K, ∀ᶠ z : (ι → ℝ) × ℝ in 𝓝 (0,x),
      0<perturb m v z.1 z.2 := by
    intro x _
    apply hF.continuousAt.eventually
    simpa [perturb] using lt_mem_nhds (hpos x)
  have hall := hK.eventually_forall_of_forall_eventually
    (P := fun a x => 0<perturb m v a x) hlocal
  filter_upwards [hall] with a ha x
  by_cases hx : x ∈ K
  · exact ha x hx
  · have hz (i) : v i x=0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun hi => hx (mem_iUnion.mpr ⟨i,hi⟩)
    simpa [perturb,hz] using hpos x

/--
Exact identity `f=0`.

Use: `«2610.05164v2».LocalObstruction.independent_normalization_directions` uses this identity
to construct witnesses satisfying `∃ w₀ w₁ : SmoothTest, testIntegral
(fun _ => 1) continuous_const w₀=1 ∧ testIntegral (fun _ => 1) continuous_const w₁=1 ∧
testIntegral g hg w₀≠testIntegral g hg w₁`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem continuous_eq_zero_of_test_integrals {f : ℝ → ℝ} (hf : Continuous f)
    (hzero : ∀ v : ℝ → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
      (∫ x, v x*f x)=0) : f=0 := by
  have he : f=ᵐ[volume] 0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    hf.locallyIntegrable (by simpa only [smul_eq_mul] using hzero)
  exact MeasureTheory.Measure.eq_of_ae_eq he hf continuous_const

end
end «2610.05164v2».LocalObstruction
