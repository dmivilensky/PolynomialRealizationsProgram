import krylov.LinearAlgebra.BudgetSupport
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Article: main_krylov, apA:galerkin(e), spectral budget duality.
Use: optimize the true output norm over actual symmetric perturbations; compactness
supplies an actual maximizing output direction in the finite-dimensional article setting.
Source: the proved symmetric budget support, finite Hölder duality and the extreme value theorem.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Finset
open scoped BigOperators InnerProductSpace NNReal
variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Directional support duality determines the exact attained output norm over genuine budgets.
Use: a common lifting applies to finite ℓ_p, simplex and box scalar allocations.
Article: main_krylov, apA:galerkin(e), exchanging the two compact optimizations.
Proof: Cauchy--Schwarz bounds each normalized output by its directional support;
the support-attaining family at a maximizing direction gives the reverse norm inequality. -/
theorem budget_norm_of_directional_support (I : Finset ι) (ω : ι → ℝ≥0)
    (B : Set (ι → ℝ≥0)) (L : ι → E →L[ℝ] F) (v : ι → E) (φ : F → ℝ≥0) (C : ℝ≥0)
    (hφ : ∀ u, ‖u‖ = 1 → IsGreatest
      ((fun a : ι → ℝ≥0 => ∑ i ∈ I, (ω i * ‖(L i).adjoint u‖₊ * ‖v i‖₊) * a i) '' B) (φ u))
    (hC : IsGreatest (φ '' {u : F | ‖u‖ = 1}) C) :
    IsGreatest {z : ℝ | ∃ T ∈ symmetricBudgetFamily I ω B,
      z = ‖∑ i ∈ I, L i (T i (v i))‖} (C : ℝ) := by
  -- Move each actual output action across its adjoint before optimizing the common direction.
  have hpair : ∀ (u : F) (T : ι → E →L[ℝ] E),
      inner ℝ u (∑ i ∈ I, L i (T i (v i))) =
        ∑ i ∈ I, inner ℝ ((L i).adjoint u) (T i (v i)) := by
    intro u T
    simp only [inner_sum, ContinuousLinearMap.adjoint_inner_left]
  have hbound : ∀ T ∈ symmetricBudgetFamily I ω B,
      ‖∑ i ∈ I, L i (T i (v i))‖ ≤ (C : ℝ) := by
    intro T hT
    let z := ∑ i ∈ I, L i (T i (v i))
    by_cases hz : z = 0
    · simpa only [show ∑ i ∈ I, L i (T i (v i)) = z from rfl, hz, norm_zero] using C.coe_nonneg
    · let u := NormedSpace.normalize z
      have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hz
      have hs := (symmetric_budget_support I ω B (fun i => (L i).adjoint u) v (φ u) (hφ u hu)).2
        ⟨T, hT, rfl⟩
      rw [← hpair, real_inner_comm, inner_normalize] at hs
      have hc : φ u ≤ C := hC.2 ⟨u, hu, rfl⟩
      exact hs.trans (by exact_mod_cast hc)
  obtain ⟨u, hu, hmax⟩ := hC.1
  change ‖u‖ = 1 at hu
  obtain ⟨T, hT, he⟩ := (symmetric_budget_support I ω B (fun i => (L i).adjoint u) v (φ u)
    (hφ u hu)).1
  have hlo : (C : ℝ) ≤ ‖∑ i ∈ I, L i (T i (v i))‖ := by
    rw [← hmax, he, ← hpair]
    simpa only [hu, one_mul] using real_inner_le_norm u (∑ i ∈ I, L i (T i (v i)))
  exact ⟨⟨T, hT, le_antisymm (hbound T hT) hlo |>.symm⟩,
    by rintro z ⟨S, hS, rfl⟩; exact hbound S hS⟩

/-- The actual finite ℓ_q support function of the output direction.
Use: the right side of the article's spectral-budget duality formula.
Article: main_krylov, apA:galerkin(e), ‖(ω_l‖L_lᵀu‖‖v_l‖)_l‖_q. -/
def spectralDirectionalSupport (I : Finset ι) (ω : ι → ℝ≥0)
    (L : ι → E →L[ℝ] F) (v : ι → E) (q : ℝ) (u : F) : ℝ≥0 :=
  (∑ i ∈ I, (ω i * ‖(L i).adjoint u‖₊ * ‖v i‖₊)^q) ^ (1 / q)

/-- The actual spectral directional support is continuous, including vanishing component budgets.
Use: compactness gives a genuine maximum over unit output directions.
Article: main_krylov, apA:galerkin(e), attainment of the dual maximum.
Proof: continuous adjoint actions, norms, nonnegative powers and finite sums compose. -/
theorem continuous_spectralDirectionalSupport (I : Finset ι) (ω : ι → ℝ≥0)
    (L : ι → E →L[ℝ] F) (v : ι → E) {q : ℝ} (hq : 0 < q) :
    Continuous (spectralDirectionalSupport I ω L v q) := by
  apply (NNReal.continuous_rpow_const (one_div_nonneg.mpr hq.le)).comp
  apply continuous_finsetSum
  intro i _
  exact (NNReal.continuous_rpow_const hq.le).comp
    ((continuous_const.mul (L i).adjoint.continuous.nnnorm).mul continuous_const)

/-- Full attained spectral duality for finite conjugate exponents and actual perturbation families.
Use: both sides of the article's finite ℓ_p/ℓ_q formula are actual maxima with witnesses.
Article: main_krylov, apA:galerkin(e), eq:budget-duality, 1<p<∞.
Proof: compactness supplies the maximizing unit direction and sharp finite Hölder
allocation supplies its actual symmetric perturbations; the general lifting gives equality. -/
theorem spectral_lp_budget_duality [FiniteDimensional ℝ F] [Nontrivial F]
    (I : Finset ι) (ω : ι → ℝ≥0) (L : ι → E →L[ℝ] F) (v : ι → E)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0,
      IsGreatest ((spectralDirectionalSupport I ω L v q) '' {u : F | ‖u‖ = 1}) C ∧
      IsGreatest {z : ℝ | ∃ T ∈ symmetricBudgetFamily I ω {a | ∑ i ∈ I, (a i)^p ≤ 1},
        z = ‖∑ i ∈ I, L i (T i (v i))‖} (C : ℝ) := by
  let φ := spectralDirectionalSupport I ω L v q
  have hs : IsCompact {u : F | ‖u‖ = 1} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : F) 1
  have hn : ({u : F | ‖u‖ = 1} : Set F).Nonempty := by
    simpa only [Metric.sphere, dist_zero_right] using
      (NormedSpace.sphere_nonempty (E := F) (x := 0)).mpr zero_le_one
  obtain ⟨C, hC⟩ := (hs.image (continuous_spectralDirectionalSupport I ω L v hpq.symm.pos)).exists_isGreatest
    (hn.image φ)
  refine ⟨C, hC, budget_norm_of_directional_support I ω _ L v φ C ?_ hC⟩
  -- The existing Hölder theorem constructs the maximizing allocation at every fixed direction.
  intro u _
  exact NNReal.isGreatest_Lp I (fun i => ω i * ‖(L i).adjoint u‖₊ * ‖v i‖₊) hpq.symm

/-- Continuous directional allocation supports attain the exact norm duality on a finite-dimensional output.
Use: compactness closes both endpoint allocation formulas through the same actual budget family.
Article: main_krylov, apA:galerkin(e), the maximum over unit output vectors.
Proof: take the extreme value of the actual support on the compact unit sphere
and use the proved directional-to-norm support lifting. -/
theorem spectral_budget_duality_of_continuous_support [FiniteDimensional ℝ F] [Nontrivial F]
    (I : Finset ι) (ω : ι → ℝ≥0) (B : Set (ι → ℝ≥0))
    (L : ι → E →L[ℝ] F) (v : ι → E) (φ : F → ℝ≥0) (hc : Continuous φ)
    (hφ : ∀ u, IsGreatest
      ((fun a : ι → ℝ≥0 => ∑ i ∈ I, (ω i * ‖(L i).adjoint u‖₊ * ‖v i‖₊) * a i) '' B) (φ u)) :
    ∃ C : ℝ≥0, IsGreatest (φ '' {u : F | ‖u‖ = 1}) C ∧
      IsGreatest {z : ℝ | ∃ T ∈ symmetricBudgetFamily I ω B,
        z = ‖∑ i ∈ I, L i (T i (v i))‖} (C : ℝ) := by
  have hs : IsCompact {u : F | ‖u‖ = 1} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : F) 1
  have hn : ({u : F | ‖u‖ = 1} : Set F).Nonempty := by
    simpa only [Metric.sphere, dist_zero_right] using
      (NormedSpace.sphere_nonempty (E := F) (x := 0)).mpr zero_le_one
  -- No maximizing direction is assumed: compactness constructs one in the genuine output space.
  obtain ⟨C, hC⟩ := (hs.image hc).exists_isGreatest (hn.image φ)
  exact ⟨C, hC, budget_norm_of_directional_support I ω B L v φ C (fun u _ => hφ u) hC⟩

/-- Full attained spectral duality for independent budgets, p=∞ and q=1.
Use: all component budgets may be spent simultaneously, including zero budgets and no increments.
Article: main_krylov, apA:galerkin(e), eq:budget-duality at p=∞.
Proof: the box-allocation support is the continuous sum of its actual adjoint norm coefficients. -/
theorem spectral_box_budget_duality [FiniteDimensional ℝ F] [Nontrivial F]
    (I : Finset ι) (ω : ι → ℝ≥0) (L : ι → E →L[ℝ] F) (v : ι → E) :
    ∃ C : ℝ≥0,
      IsGreatest ((fun u : F => ∑ i ∈ I, ω i * ‖(L i).adjoint u‖₊ * ‖v i‖₊) ''
        {u : F | ‖u‖ = 1}) C ∧
      IsGreatest {z : ℝ | ∃ T ∈ symmetricBudgetFamily I ω {a | ∀ i ∈ I, a i ≤ 1},
        z = ‖∑ i ∈ I, L i (T i (v i))‖} (C : ℝ) := by
  apply spectral_budget_duality_of_continuous_support
  · apply continuous_finsetSum
    intro i _
    exact (continuous_const.mul (L i).adjoint.continuous.nnnorm).mul continuous_const
  · intro u
    exact box_allocation_support I (fun i => ω i * ‖(L i).adjoint u‖₊ * ‖v i‖₊)

/-- Full attained spectral duality for a summed budget, p=1 and q=∞.
Use: the actual uncertainty maximum agrees with the largest adjoint coefficient at its best direction.
Article: main_krylov, apA:galerkin(e), eq:budget-duality at p=1.
Proof: the simplex support is the continuous finite maximum of its actual coefficients. -/
theorem spectral_simplex_budget_duality [FiniteDimensional ℝ F] [Nontrivial F]
    (I : Finset ι) (ω : ι → ℝ≥0) (L : ι → E →L[ℝ] F) (v : ι → E) :
    ∃ C : ℝ≥0,
      IsGreatest ((fun u : F => I.sup (fun i => ω i * ‖(L i).adjoint u‖₊ * ‖v i‖₊)) ''
        {u : F | ‖u‖ = 1}) C ∧
      IsGreatest {z : ℝ | ∃ T ∈ symmetricBudgetFamily I ω {a | ∑ i ∈ I, a i ≤ 1},
        z = ‖∑ i ∈ I, L i (T i (v i))‖} (C : ℝ) := by
  apply spectral_budget_duality_of_continuous_support
  · apply Continuous.finset_sup_apply
    intro i _
    exact (continuous_const.mul (L i).adjoint.continuous.nnnorm).mul continuous_const
  · intro u
    exact simplex_allocation_support I (fun i => ω i * ‖(L i).adjoint u‖₊ * ‖v i‖₊)

end
end krylov.LinearAlgebra
