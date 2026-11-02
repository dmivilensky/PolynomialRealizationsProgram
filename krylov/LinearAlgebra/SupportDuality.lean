import krylov.LinearAlgebra.BudgetSupport
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Article: main_krylov, apA:galerkin(e), common support duality.
Use: lift proved individual uncertainty-ball supports through actual scalar
budget allocations and then optimize the true output norm in a finite-dimensional space.
Source: sharp scalar support, Cauchy--Schwarz and the extreme value theorem.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Finset
open scoped BigOperators InnerProductSpace NNReal
variable {ι P : Type*}

/-- The actual perturbation families obtained by feasible nonnegative budget allocations.
Use: one definition permits spectral and Frobenius balls without identifying their norms.
Article: main_krylov, apA:galerkin(e). -/
def allocatedFamily (I : Finset ι) (ω : ι → ℝ≥0) (B : Set (ι → ℝ≥0))
    (ball : ι → ℝ≥0 → Set P) : Set (ι → P) :=
  {T | ∃ a ∈ B, ∀ i ∈ I, T i ∈ ball i (ω i * a i)}

/-- Nonnegative allocation certificates are exactly normalized ℓ_p radius constraints,
with zero physical budgets forcing zero actual radii.
Use: connect both concrete uncertainty norms to the same original budget convention.
Article: main_krylov, apA:galerkin(e), zero-budget interpretation.
Proof: divide a feasible allocation at each nonzero budget and use power monotonicity;
conversely allocate the actual normalized radius at every coordinate. -/
theorem lp_allocation_iff (I : Finset ι) (ω ρ : ι → ℝ≥0) {p : ℝ} (hp : 0 ≤ p) :
    (∃ a : ι → ℝ≥0, (∑ i ∈ I, (a i)^p ≤ 1) ∧ ∀ i ∈ I, ρ i ≤ ω i * a i) ↔
      (∀ i ∈ I, ω i = 0 → ρ i = 0) ∧ ∑ i ∈ I, (ρ i / ω i)^p ≤ 1 := by
  constructor
  · rintro ⟨a, ha, hb⟩
    refine ⟨fun i hi hz => ?_, (sum_le_sum (fun i hi => NNReal.rpow_le_rpow ?_ hp)).trans ha⟩
    · have h := hb i hi
      rw [hz, zero_mul, nonpos_iff_eq_zero] at h
      exact h
    · by_cases hz : ω i = 0
      · simp only [hz, div_zero, zero_le]
      · exact (div_le_iff₀ (pos_iff_ne_zero.mpr hz)).mpr (by simpa only [mul_comm] using hb i hi)
  · rintro ⟨hz, hb⟩
    refine ⟨(fun i => ρ i / ω i), hb, fun i hi => ?_⟩
    -- This allocation uses the actual radius rather than an assumed maximizing radius.
    by_cases hw : ω i = 0
    · simp only [hz i hi hw, hw, zero_mul, le_refl]
    · rw [mul_div_cancel₀ _ hw]

/-- Exact individual uncertainty supports lift to the exact allocated-family support.
Use: reuse the same Hölder, box and simplex allocation theorems for distinct actual norms.
Article: main_krylov, apA:galerkin(e).
Proof: construct an actual ball maximizer for every coordinate at a maximizing
allocation; every other feasible family has an allocating certificate giving the same upper bound. -/
theorem allocated_support (I : Finset ι) (ω ν : ι → ℝ≥0) (B : Set (ι → ℝ≥0))
    (ball : ι → ℝ≥0 → Set P) (f : ι → P → ℝ)
    (hball : ∀ i r, IsGreatest (f i '' ball i r) ((r * ν i : ℝ≥0) : ℝ))
    (C : ℝ≥0) (hC : IsGreatest ((fun a => ∑ i ∈ I, (ω i * ν i) * a i) '' B) C) :
    IsGreatest ((fun T : ι → P => ∑ i ∈ I, f i (T i)) '' allocatedFamily I ω B ball) (C : ℝ) := by
  obtain ⟨a, ha, hmax⟩ := hC.1
  have hlocal : ∀ i, ∃ t ∈ ball i (ω i * a i), f i t = ((ω i * a i * ν i : ℝ≥0) : ℝ) := by
    intro i
    exact (hball i (ω i * a i)).1
  choose T hT hval using hlocal
  have he : ∀ b : ι → ℝ≥0, (∑ i ∈ I, ((ω i * b i * ν i : ℝ≥0) : ℝ)) =
      ((∑ i ∈ I, (ω i * ν i) * b i : ℝ≥0) : ℝ) := by
    intro b
    simp only [NNReal.coe_sum, NNReal.coe_mul]
    apply sum_congr rfl
    intro i _
    ring
  constructor
  · refine ⟨T, ⟨a, ha, fun i _ => hT i⟩, ?_⟩
    change (∑ i ∈ I, f i (T i)) = (C : ℝ)
    rw [sum_congr rfl (fun i _ => hval i), he]
    exact_mod_cast hmax
  · rintro z ⟨S, ⟨b, hb, hS⟩, rfl⟩
    -- An actual family's certificate controls its scalar support at every coordinate.
    have hi : ∀ i ∈ I, f i (S i) ≤ ((ω i * b i * ν i : ℝ≥0) : ℝ) :=
      fun i hi => (hball i (ω i * b i)).2 ⟨S i, hS i hi, rfl⟩
    apply (sum_le_sum hi).trans
    rw [he]
    exact_mod_cast hC.2 ⟨b, hb, rfl⟩

section Output
variable {F X : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Exact directional supports determine the exact attained norm on the same actual scenario set.
Use: exchange the two maxima only after their genuine directional supports have been proved.
Article: main_krylov, apA:galerkin(e).
Proof: normalize each nonzero actual output for the upper bound; a support
maximizer at a maximizing unit direction supplies the reverse norm inequality. -/
theorem norm_maximum_of_support (S : Set X) (out : X → F) (φ : F → ℝ≥0) (C : ℝ≥0)
    (hφ : ∀ u, ‖u‖ = 1 → IsGreatest ((fun T => inner ℝ u (out T)) '' S) (φ u : ℝ))
    (hC : IsGreatest (φ '' {u : F | ‖u‖ = 1}) C) :
    IsGreatest ((fun T => ‖out T‖) '' S) (C : ℝ) := by
  have hb : ∀ T ∈ S, ‖out T‖ ≤ (C : ℝ) := by
    intro T hT
    by_cases hz : out T = 0
    · simpa only [hz, norm_zero] using C.coe_nonneg
    · let u := NormedSpace.normalize (out T)
      have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hz
      have hs := (hφ u hu).2 ⟨T, hT, rfl⟩
      change inner ℝ u (out T) ≤ (φ u : ℝ) at hs
      rw [real_inner_comm, inner_normalize] at hs
      exact hs.trans (by exact_mod_cast hC.2 ⟨u, hu, rfl⟩)
  -- Use an actually attained directional maximum to construct a norm-attaining scenario.
  obtain ⟨u, hu, hc⟩ := hC.1
  change ‖u‖ = 1 at hu
  obtain ⟨T, hT, ht⟩ := (hφ u hu).1
  have hlo : (C : ℝ) ≤ ‖out T‖ := by
    rw [← hc, ← ht]
    simpa only [hu, one_mul] using real_inner_le_norm u (out T)
  exact ⟨⟨T, hT, le_antisymm (hb T hT) hlo⟩, by rintro z ⟨T, hT, rfl⟩; exact hb T hT⟩

/-- Continuous directional supports have genuine norm and directional maxima in finite dimension.
Use: the common compactness step for every admitted perturbation budget norm.
Article: main_krylov, apA:galerkin(e).
Proof: construct the maximum of the actual continuous support on the compact
nonempty unit sphere, then apply the proved support-to-norm maximum theorem. -/
theorem norm_duality_of_continuous_support [FiniteDimensional ℝ F] [Nontrivial F]
    (S : Set X) (out : X → F) (φ : F → ℝ≥0) (hc : Continuous φ)
    (hφ : ∀ u, IsGreatest ((fun T => inner ℝ u (out T)) '' S) (φ u : ℝ)) :
    ∃ C : ℝ≥0, IsGreatest (φ '' {u : F | ‖u‖ = 1}) C ∧
      IsGreatest ((fun T => ‖out T‖) '' S) (C : ℝ) := by
  -- Compactness constructs the maximizing direction instead of assuming its existence.
  have hs : IsCompact {u : F | ‖u‖ = 1} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : F) 1
  have hn : ({u : F | ‖u‖ = 1} : Set F).Nonempty := by
    simpa only [Metric.sphere, dist_zero_right] using
      (NormedSpace.sphere_nonempty (E := F) (x := 0)).mpr zero_le_one
  obtain ⟨C, hC⟩ := (hs.image hc).exists_isGreatest (hn.image φ)
  exact ⟨C, hC, norm_maximum_of_support S out φ C (fun u _ => hφ u) hC⟩

end Output
end
end krylov.LinearAlgebra
