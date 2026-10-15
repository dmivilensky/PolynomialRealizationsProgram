import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
Article: 2610.05164v2, Theorem 3.4.
Endpoint extension on the closed filter triangle, including the degenerate triangle at scale zero.
Use: `«2610.05164v2».Comparison.filterTriangle_closure_strip` feeds
`«2610.05164v2».Comparison.Profile.determinantPotential_lipschitz` (determinant Potential
lipschitz).
Proof chain: `«2610.05164v2».Comparison.Profile.signed_determinant_comparison` — 2610.05164v2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace «2610.05164v2».Comparison
noncomputable section
open Set Filter
open scoped Topology

/--
Defines `filterTriangle` of type `Set (ℝ × ℝ)` by `{p | p.1 ∈ Icc (0:ℝ) 2 ∧ 0 ≤ p.2 ∧ p.2 ≤
a*p.1}`.

Use: `«2610.05164v2».Comparison.filterTriangle_closure_strip` uses this definition to establish
exact identity `closure (filterTriangle a ∩ {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 2})=filterTriangle a`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def filterTriangle (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (0:ℝ) 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ a*p.1}

/--
The precise assertion is `IsClosed (filterTriangle a)`.

Use: `«2610.05164v2».Comparison.filterTriangle_closure_strip` uses this assertion to establish
exact identity `closure (filterTriangle a ∩ {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 2})=filterTriangle a`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem filterTriangle_closed (a : ℝ) : IsClosed (filterTriangle a) :=
  (isClosed_Icc.preimage continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd (continuous_const.mul continuous_fst)))

/--
The precise assertion is `Convex ℝ (filterTriangle a)`.

Use: `«2610.05164v2».Comparison.filterTriangle_closure_strip` uses this assertion to establish
exact identity `closure (filterTriangle a ∩ {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 2})=filterTriangle a`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem filterTriangle_convex (a : ℝ) : Convex ℝ (filterTriangle a) := by
  intro x hx y hy u v hu hv huv
  change (u*x.1+v*y.1 ∈ Icc (0:ℝ) 2) ∧ 0 ≤ u*x.2+v*y.2 ∧
    u*x.2+v*y.2 ≤ a*(u*x.1+v*y.1)
  refine ⟨⟨add_nonneg (mul_nonneg hu hx.1.1) (mul_nonneg hv hy.1.1),?_⟩,
    add_nonneg (mul_nonneg hu hx.2.1) (mul_nonneg hv hy.2.1),?_⟩
  · nlinarith [mul_nonneg hu (sub_nonneg.mpr hx.1.2),mul_nonneg hv (sub_nonneg.mpr hy.1.2)]
  · nlinarith [mul_nonneg hu (sub_nonneg.mpr hx.2.2),mul_nonneg hv (sub_nonneg.mpr hy.2.2)]

/--
Exact identity `closure (filterTriangle a ∩ {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 2})=filterTriangle a`.

Use: `«2610.05164v2».Comparison.Profile.determinantPotential_lipschitz` uses this identity to
establish the displayed Lipschitz bound: `LipschitzOnWith (Real.toNNReal
(P.determinantLipschitzConstant s)) (fun p : ℝ × ℝ => P.determinantPotential hκ s p.1 p.2)
(filterTriangle (s/κ))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem filterTriangle_closure_strip {a : ℝ} (ha : 0 ≤ a) :
    closure (filterTriangle a ∩ {p : ℝ × ℝ | p.1 ∈ Ioo (0:ℝ) 2})=filterTriangle a := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply subset_antisymm
  · exact closure_minimal inter_subset_left (filterTriangle_closed a)
  · intro p hp
    let z : ℝ × ℝ := (1,0)
    have hz : z ∈ filterTriangle a := ⟨by norm_num [z],by norm_num [z],by simpa [z] using ha⟩
    let f : ℝ → ℝ × ℝ := fun t => (1-t) • p+t • z
    -- Record the convergence ht with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have ht : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 p) := by
      have hc : Continuous f := by dsimp [f]; fun_prop
      have ht0 : Tendsto f (𝓝 (0:ℝ)) (𝓝 (f 0)) := hc.continuousAt.tendsto
      simpa only [f,sub_zero,one_smul,zero_smul,add_zero] using ht0.mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto ht
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    refine ⟨(filterTriangle_convex a) hp hz (by linarith [ht.2]) ht.1.le (by ring),?_⟩
    change (1-t)*p.1+t*1 ∈ Ioo (0:ℝ) 2
    constructor
    · nlinarith [ht.1,mul_nonneg (show 0 ≤ 1-t by linarith [ht.2]) hp.1.1]
    · nlinarith [ht.1,ht.2,mul_nonneg (show 0 ≤ 1-t by linarith [ht.2]) (sub_nonneg.mpr hp.1.2)]

end
end «2610.05164v2».Comparison
