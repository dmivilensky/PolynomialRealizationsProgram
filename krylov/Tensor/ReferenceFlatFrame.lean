import krylov.Tensor.FlatReversal
import krylov.Tensor.ReferenceAmplification
import krylov.Reference.EnergyPositive

/-!
Article: main_krylov, apG:flat, the actual computed flat CG reference.
Use: derive the genuine normalized orthogonal flat midpoint/tail vectors
from equal actual CG step energies, including the exact scalar factor c.
Source: the proved exact CG frame, energy identity and terminal telescoping.
-/

namespace krylov.Tensor
noncomputable section
open krylov.Reference krylov.Variation Matrix Finset
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every true flat CG step is sqrt c times its actual computed unit step.
Article: main_krylov, apG:flat. -/
theorem flat_canonical_step (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hf : ∀ i : Fin (referenceAtomCount A hA g), cgEnergy A g i.val = c)
    (i : Fin (referenceAtomCount A hA g)) :
    canonicalCGStep A g i.val = Real.sqrt c • canonicalCGUnitStep A g i.val := by
  have hs : ‖canonicalCGStep A g i.val‖^2 = c := (cgEnergy_eq_norm_sq A hA g i.val).symm.trans (hf i)
  have hc : 0 ≤ c := hs ▸ sq_nonneg _
  have hn : ‖canonicalCGStep A g i.val‖ = Real.sqrt c :=
    (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (hs.trans (Real.sq_sqrt hc).symm)
  rw [← hn]
  exact (NormedSpace.norm_smul_normalize _).symm

/-- A nonempty actual flat CG profile has strictly positive common energy.
Article: main_krylov, apG:flat. -/
theorem flat_cg_energy_pos (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hf : ∀ i : Fin (referenceAtomCount A hA g), cgEnergy A g i.val = c)
    (hN : 0 < referenceAtomCount A hA g) : 0 < c := by
  rw [← hf ⟨0, hN⟩]
  exact cgEnergy_pos A hA g 0 hN

/-- The actual flat midpoint drift has its exact normalized flat factor.
Article: main_krylov, apG:flat. -/
theorem reference_flat_midpoint (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hf : ∀ i : Fin (referenceAtomCount A hA g), cgEnergy A g i.val = c)
    (l : Fin (referenceAtomCount A hA g - 1)) :
    referenceMidpointDrift A g l.val = Real.sqrt c • flatForwardMidpoint
      (fun i : Fin (referenceAtomCount A hA g) => canonicalCGUnitStep A g i.val) l := by
  have hl : l.val < referenceAtomCount A hA g := by have := l.isLt; omega
  have hl1 : l.val+1 < referenceAtomCount A hA g := by have := l.isLt; omega
  rw [referenceMidpointDrift, flat_canonical_step A hA g c hf ⟨l.val, hl⟩,
    flat_canonical_step A hA g c hf ⟨l.val+1, hl1⟩]
  simp only [flatForwardMidpoint, flatExtend, dite_eq_left hl, dite_eq_left hl1,
    smul_add, smul_smul]
  module

/-- An actual finite CG suffix is precisely its chronological finite tail.
Article: main_krylov, apG:flat. -/
theorem flat_fin_tail_sum {E : Type*} [AddCommMonoid E] (N l : ℕ) (f : ℕ → E) :
    (∑ i : Fin N, if l < i.val then f i.val else 0) = ∑ i ∈ Ico (l+1) N, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if l < i then f i else 0), ← sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [mem_filter, mem_range, mem_Ico]
  omega

/-- The actual remaining CG displacement has the exact normalized flat tail.
Article: main_krylov, apG:flat. -/
theorem reference_flat_tail (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hf : ∀ i : Fin (referenceAtomCount A hA g), cgEnergy A g i.val = c)
    (l : Fin (referenceAtomCount A hA g - 1)) :
    remainingTail A g l.val = Real.sqrt c • flatForwardTail
      (fun i : Fin (referenceAtomCount A hA g) => canonicalCGUnitStep A g i.val) l := by
  rw [remainingTail_eq_sum A hA g l.val (by have := l.isLt; omega)]
  rw [← flat_fin_tail_sum]
  simp only [flatForwardTail, smul_sum, smul_ite, smul_zero]
  apply sum_congr rfl
  intro i _
  rw [flat_canonical_step A hA g c hf i]

/-- Scaling both actual compatible vector slots scales the real response by
the square of that scalar. Article: main_krylov, apG:flat. -/
theorem flagResponse_scale {ι κ E : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : ι → E) (I : κ → Finset ι) (ξ v : κ → E)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (r : ℝ) :
    flagResponse e I (fun l => r • ξ l) (fun l => r • v l) f = r^2 • flagResponse e I ξ v f := by
  unfold flagResponse
  simp only [← cubicCurried_apply, map_smul, _root_.smul_apply, smul_eq_mul, smul_sum, smul_smul]
  apply sum_congr rfl
  intro l _
  apply sum_congr rfl
  intro i _
  congr 1
  ring

/-- The genuine reference response under a flat actual energy profile is
exactly c times its genuine normalized chronological flat response.
Article: main_krylov, apG:flat. -/
theorem reference_flat_response (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hf : ∀ i : Fin (referenceAtomCount A hA g), cgEnergy A g i.val = c)
    (hc : 0 ≤ c)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ) :
    referenceCubicResponse A hA g f = c • flagResponse
      (fun i : Fin (referenceAtomCount A hA g) => canonicalCGUnitStep A g i.val)
      (flatForwardFlag _)
      (flatForwardMidpoint (fun i : Fin (referenceAtomCount A hA g) => canonicalCGUnitStep A g i.val))
      (flatForwardTail (fun i : Fin (referenceAtomCount A hA g) => canonicalCGUnitStep A g i.val)) f := by
  unfold referenceCubicResponse
  simp_rw [reference_flat_midpoint A hA g c hf, reference_flat_tail A hA g c hf]
  rw [flagResponse_scale, Real.sq_sqrt hc]
  rfl

end
end krylov.Tensor
