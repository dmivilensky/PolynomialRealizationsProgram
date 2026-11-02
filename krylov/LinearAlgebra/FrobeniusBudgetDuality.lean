import krylov.LinearAlgebra.FrobeniusSupport
import krylov.LinearAlgebra.SupportDuality
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
Article: main_krylov, apA:galerkin(e), full Frobenius budget duality.
Use: actual symmetric matrix perturbations carry the earlier article's genuine
Hilbert--Schmidt norm; their adjoint coefficient is the symmetric outer-product norm.
Source: the proved Frobenius ball support, sharp finite scalar budget allocation,
and the common compact support-to-norm duality.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix Finset chebyshev1
open scoped Matrix InnerProductSpace BigOperators NNReal
variable {ι F : Type*} {n : ℕ} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The actual symmetric Hilbert--Schmidt perturbation ball.
Use: no spectral or entrywise norm is substituted for the Frobenius budget.
Article: main_krylov, apA:galerkin(e). -/
def frobeniusBall (r : ℝ≥0) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {E | E.IsSymm ∧ hsNorm E ≤ (r : ℝ)}

/-- The exact support of the actual Frobenius ball, in common image form.
Use: feed its constructed symmetric maximizing matrix into the shared budget lifting.
Article: main_krylov, apA:galerkin(e), Frobenius support.
Proof: the proved Frobenius support supplies both an actual maximizer and every upper bound. -/
theorem frobenius_ball_support_image (u v : Fin n → ℝ) (r : ℝ≥0) :
    IsGreatest ((fun E => u ⬝ᵥ (E *ᵥ v)) '' frobeniusBall r)
      ((r * ‖frobeniusVector (symmetricOuter u v)‖₊ : ℝ≥0) : ℝ) := by
  have h := frobenius_ball_support u v r.coe_nonneg
  rw [NNReal.coe_mul, coe_nnnorm, norm_frobeniusVector]
  constructor
  · obtain ⟨E, hs, hn, he⟩ := h.1
    exact ⟨E, ⟨hs, hn⟩, he.symm⟩
  · rintro z ⟨E, ⟨hs, hn⟩, rfl⟩
    exact h.2 ⟨E, hs, hn, rfl⟩

/-- The true Frobenius adjoint coefficient at an output direction.
Use: exactly the norm replacing ‖L_lᵀu‖‖v_l‖ in the article's dual formula.
Article: main_krylov, apA:galerkin(e), ‖sym(L_lᵀu⊗v_l)‖_F. -/
def frobeniusCoefficient (L : EuclideanSpace ℝ (Fin n) →L[ℝ] F) (v : Fin n → ℝ) (u : F) : ℝ≥0 :=
  ‖frobeniusVector (symmetricOuter (WithLp.ofLp (L.adjoint u)) v)‖₊

/-- The actual Frobenius coefficient is continuous at every output direction.
Use: the dual maximum exists even when individual supports or budgets vanish.
Article: main_krylov, apA:galerkin(e), compact dual maximum.
Proof: each flattened matrix entry is linear in the continuous actual adjoint action. -/
theorem continuous_frobeniusCoefficient (L : EuclideanSpace ℝ (Fin n) →L[ℝ] F) (v : Fin n → ℝ) :
    Continuous (frobeniusCoefficient L v) := by
  -- Continuity is checked in genuine flattened matrix coordinates before taking its norm.
  apply Continuous.nnnorm
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n × Fin n => ℝ)).comp
  apply continuous_pi
  intro ij
  change Continuous (fun u : F => (1 / 2 : ℝ) *
    ((L.adjoint u) ij.1 * v ij.2 + v ij.1 * (L.adjoint u) ij.2))
  have hi : Continuous (fun u : F => (L.adjoint u) ij.1) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) ij.1).comp L.adjoint.continuous
  have hj : Continuous (fun u : F => (L.adjoint u) ij.2) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin n => ℝ) ij.2).comp L.adjoint.continuous
  exact continuous_const.mul ((hi.mul continuous_const).add (continuous_const.mul hj))

/-- The actual vector output of a symmetric matrix perturbation family.
Use: the primal quantity T(E)=∑L_lE_lv_l in the source, in genuine Euclidean coordinates.
Article: main_krylov, apA:galerkin(e). -/
def frobeniusBudgetOutput (I : Finset ι) (L : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] F)
    (v : ι → Fin n → ℝ) (E : ι → Matrix (Fin n) (Fin n) ℝ) : F :=
  ∑ i ∈ I, L i (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (E i) (WithLp.toLp 2 (v i)))

/-- Actual Frobenius families have exactly their scalar allocated support at every output direction.
Use: the Frobenius coefficient is used with actual matrix perturbations before optimizing norms.
Article: main_krylov, apA:galerkin(e), Frobenius budget support.
Proof: move the true output action through its actual adjoint, then apply the
constructed symmetric Frobenius ball support and shared scalar allocation lifting. -/
theorem frobenius_allocated_support (I : Finset ι) (ω : ι → ℝ≥0) (B : Set (ι → ℝ≥0))
    (L : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] F) (v : ι → Fin n → ℝ) (u : F) (C : ℝ≥0)
    (hC : IsGreatest ((fun a => ∑ i ∈ I, (ω i * frobeniusCoefficient (L i) (v i) u) * a i) '' B) C) :
    IsGreatest ((fun E => inner ℝ u (frobeniusBudgetOutput I L v E)) ''
      allocatedFamily I ω B (fun _ => frobeniusBall)) (C : ℝ) := by
  -- Apply the adjoint identity once per outer output action, before evaluating its matrix action.
  have hpair : ∀ E : ι → Matrix (Fin n) (Fin n) ℝ,
      inner ℝ u (frobeniusBudgetOutput I L v E) =
        ∑ i ∈ I, (WithLp.ofLp ((L i).adjoint u)) ⬝ᵥ (E i *ᵥ v i) := by
    intro E
    simp only [frobeniusBudgetOutput, inner_sum]
    apply sum_congr rfl
    intro i _
    rw [← (L i).adjoint_inner_left, Matrix.inner_toEuclideanCLM]
  have h := allocated_support I ω (fun i => frobeniusCoefficient (L i) (v i) u) B
    (fun _ => frobeniusBall) (fun i E => (WithLp.ofLp ((L i).adjoint u)) ⬝ᵥ (E *ᵥ v i))
    (fun i r => frobenius_ball_support_image _ _ r) C hC
  simpa only [hpair] using h

/-- Full actual Frobenius budget duality follows from a continuous sharp scalar allocation support.
Use: a single compactness theorem treats finite exponents, p=1 and p=∞.
Article: main_krylov, apA:galerkin(e), Frobenius eq:budget-duality.
Proof: the actual allocated matrix support is already proved at every direction;
the shared finite-dimensional maximum theorem constructs both genuine maxima. -/
theorem frobenius_budget_duality_of_support [FiniteDimensional ℝ F] [Nontrivial F]
    (I : Finset ι) (ω : ι → ℝ≥0) (B : Set (ι → ℝ≥0))
    (L : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] F) (v : ι → Fin n → ℝ)
    (φ : F → ℝ≥0) (hc : Continuous φ)
    (hφ : ∀ u, IsGreatest
      ((fun a => ∑ i ∈ I, (ω i * frobeniusCoefficient (L i) (v i) u) * a i) '' B) (φ u)) :
    ∃ C : ℝ≥0, IsGreatest (φ '' {u : F | ‖u‖ = 1}) C ∧
      IsGreatest ((fun E => ‖frobeniusBudgetOutput I L v E‖) ''
        allocatedFamily I ω B (fun _ => frobeniusBall)) (C : ℝ) :=
  norm_duality_of_continuous_support _ _ φ hc
    (fun u => frobenius_allocated_support I ω B L v u (φ u) (hφ u))

/-- Full attained Frobenius duality for finite conjugate exponents.
Use: the article's Frobenius ℓ_p uncertainty maximum has an actual maximizing
direction and actual symmetric matrix perturbations.
Article: main_krylov, apA:galerkin(e), Frobenius eq:budget-duality, 1<p<∞.
Proof: the symmetric outer-product coefficient is continuous; the proved Hölder
allocation is exact, and the common actual-matrix support theorem closes both maxima. -/
theorem frobenius_lp_budget_duality [FiniteDimensional ℝ F] [Nontrivial F]
    (I : Finset ι) (ω : ι → ℝ≥0) (L : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] F)
    (v : ι → Fin n → ℝ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0,
      IsGreatest ((fun u : F => (∑ i ∈ I, (ω i * frobeniusCoefficient (L i) (v i) u)^q) ^ (1 / q)) ''
        {u : F | ‖u‖ = 1}) C ∧
      IsGreatest ((fun E => ‖frobeniusBudgetOutput I L v E‖) ''
        allocatedFamily I ω {a | ∑ i ∈ I, (a i)^p ≤ 1} (fun _ => frobeniusBall)) (C : ℝ) := by
  apply frobenius_budget_duality_of_support
  · apply (NNReal.continuous_rpow_const (one_div_nonneg.mpr hpq.symm.nonneg)).comp
    apply continuous_finsetSum
    intro i _
    exact (NNReal.continuous_rpow_const hpq.symm.nonneg).comp
      (continuous_const.mul (continuous_frobeniusCoefficient (L i) (v i)))
  · intro u
    exact NNReal.isGreatest_Lp I (fun i => ω i * frobeniusCoefficient (L i) (v i) u) hpq.symm

/-- Full attained Frobenius duality for independent budgets, including zero budgets.
Use: the p=∞ endpoint has the sum of the symmetric outer-product supports.
Article: main_krylov, apA:galerkin(e), Frobenius eq:budget-duality at p=∞.
Proof: the actual Frobenius coefficient sum is continuous and the all-ones allocation attains its support. -/
theorem frobenius_box_budget_duality [FiniteDimensional ℝ F] [Nontrivial F]
    (I : Finset ι) (ω : ι → ℝ≥0) (L : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] F)
    (v : ι → Fin n → ℝ) :
    ∃ C : ℝ≥0,
      IsGreatest ((fun u : F => ∑ i ∈ I, ω i * frobeniusCoefficient (L i) (v i) u) ''
        {u : F | ‖u‖ = 1}) C ∧
      IsGreatest ((fun E => ‖frobeniusBudgetOutput I L v E‖) ''
        allocatedFamily I ω {a | ∀ i ∈ I, a i ≤ 1} (fun _ => frobeniusBall)) (C : ℝ) := by
  apply frobenius_budget_duality_of_support
  · apply continuous_finsetSum
    intro i _
    exact continuous_const.mul (continuous_frobeniusCoefficient (L i) (v i))
  · intro u
    exact box_allocation_support I (fun i => ω i * frobeniusCoefficient (L i) (v i) u)

/-- Full attained Frobenius duality for a summed budget, including the empty index set.
Use: the p=1 endpoint has the largest symmetric outer-product support coefficient.
Article: main_krylov, apA:galerkin(e), Frobenius eq:budget-duality at p=1.
Proof: the actual finite coefficient maximum is continuous and a maximizing coordinate attains its support. -/
theorem frobenius_simplex_budget_duality [FiniteDimensional ℝ F] [Nontrivial F]
    (I : Finset ι) (ω : ι → ℝ≥0) (L : ι → EuclideanSpace ℝ (Fin n) →L[ℝ] F)
    (v : ι → Fin n → ℝ) :
    ∃ C : ℝ≥0,
      IsGreatest ((fun u : F => I.sup (fun i => ω i * frobeniusCoefficient (L i) (v i) u)) ''
        {u : F | ‖u‖ = 1}) C ∧
      IsGreatest ((fun E => ‖frobeniusBudgetOutput I L v E‖) ''
        allocatedFamily I ω {a | ∑ i ∈ I, a i ≤ 1} (fun _ => frobeniusBall)) (C : ℝ) := by
  apply frobenius_budget_duality_of_support
  · apply Continuous.finset_sup_apply
    intro i _
    exact continuous_const.mul (continuous_frobeniusCoefficient (L i) (v i))
  · intro u
    exact simplex_allocation_support I (fun i => ω i * frobeniusCoefficient (L i) (v i) u)

/-- The actual allocated Frobenius family is exactly the original normalized norm budget,
with zero budgets forcing the physical matrix perturbations to vanish.
Use: the attained Frobenius duality theorems describe the source uncertainty class exactly.
Article: main_krylov, apA:galerkin(e), original Frobenius ℓ_p constraints.
Proof: use the common scalar allocation equivalence on the actual flattened
matrix norms; their proved faithful entry representation discharges zero budgets. -/
theorem frobenius_lp_family_iff (I : Finset ι) (ω : ι → ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (E : ι → Matrix (Fin n) (Fin n) ℝ) :
    E ∈ allocatedFamily I ω {a | ∑ i ∈ I, (a i)^p ≤ 1} (fun _ => frobeniusBall) ↔
      (∀ i ∈ I, (E i).IsSymm ∧ (ω i = 0 → E i = 0)) ∧
      ∑ i ∈ I, (‖frobeniusVector (E i)‖₊ / ω i)^p ≤ 1 := by
  constructor
  · rintro ⟨a, ha, hE⟩
    have hb : ∀ i ∈ I, ‖frobeniusVector (E i)‖₊ ≤ ω i * a i := by
      intro i hi
      have h := (hE i hi).2
      rw [← norm_frobeniusVector] at h
      exact_mod_cast h
    have hs := (lp_allocation_iff I ω (fun i => ‖frobeniusVector (E i)‖₊) hp).mp ⟨a, ha, hb⟩
    refine ⟨fun i hi => ⟨(hE i hi).1, fun hz => ?_⟩, hs.2⟩
    exact (frobeniusVector_eq_zero_iff _).mp (nnnorm_eq_zero.mp (hs.1 i hi hz))
  · rintro ⟨hE, hb⟩
    have hz : ∀ i ∈ I, ω i = 0 → ‖frobeniusVector (E i)‖₊ = 0 := by
      intro i hi hw
      exact nnnorm_eq_zero.mpr ((frobeniusVector_eq_zero_iff _).mpr ((hE i hi).2 hw))
    obtain ⟨a, ha, hbound⟩ := (lp_allocation_iff I ω (fun i => ‖frobeniusVector (E i)‖₊) hp).mpr ⟨hz, hb⟩
    refine ⟨a, ha, fun i hi => ⟨(hE i hi).1, ?_⟩⟩
    -- Norm flattening identifies the scalar certificate with the actual Hilbert--Schmidt budget.
    rw [← norm_frobeniusVector]
    exact_mod_cast hbound i hi

end
end krylov.LinearAlgebra
