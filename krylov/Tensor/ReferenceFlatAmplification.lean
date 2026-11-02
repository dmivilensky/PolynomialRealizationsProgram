import krylov.Tensor.ReferenceFlatFrame
import krylov.Tensor.FlatLower

/-!
Article: main_krylov, apG:flat, the actual flat tensor amplification theorem.
Use: specialize the genuine attained reference coefficient to equal actual
CG energies, deriving both printed bounds from the genuine cubic ball.
Source: actual finite CG geometry, the genuine dyadic decomposition and
the explicit sharp flat witness.
-/

/-!
Article: krylov, Proposition E.12 [apG:flat].

The actual equal-energy CG profile has the printed tensor lower/upper bounds and exact
independent-operator square-root sum with its integral lower estimate.
The factor c is an actual positive common CG energy under the nonexhausted n≥2 reference
hypothesis.
-/

namespace krylov.Tensor
noncomputable section
open krylov.Reference krylov.Variation krylov.Functions Matrix Finset
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator NNReal

/-- Actual chronological flat flags possess the printed genuine lower cubic.
Article: main_krylov, apG:flat. -/
theorem flat_forward_lower_witness {N : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e : Fin N → E) (he : Orthonormal ℝ e) (hN : 2 ≤ N) :
    ∃ T : SymmetricCubic E,
      (∀ x : E, ‖x‖ = 1 → |T.form x x x| ≤ 2) ∧
      (Real.sqrt 3 / 2) * (N-1 : ℕ) ≤
        ‖flagResponse e (flatForwardFlag N) (flatForwardMidpoint e) (flatForwardTail e)
          (cubicUncurried T)‖ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  obtain ⟨T, hd, hb⟩ := flat_prefix_lower_witness (fun a : Fin (m+1) => e a.rev)
    (he.comp Fin.rev Fin.rev_injective) (by omega : 1 ≤ m)
  refine ⟨T, hd, ?_⟩
  rw [flatForwardResponse_eq]
  simpa only [Nat.succ_sub_one] using hb

/-- Genuine currying followed by uncurrying preserves the original actual form.
Article: main_krylov, apG:flat. -/
theorem cubicUncurried_symmetricCubic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (hf : IsSymmetricForm f) :
    cubicUncurried (symmetricCubicOfMultilinear f hf) = f := by
  ext v
  change cubicCurried f (v 0) (v 1) (v 2) = f v
  rw [cubicCurried_apply]
  congr 1
  ext i
  fin_cases i <;> rfl

variable {n : ℕ}

/-- Every actual admissible cubic has the printed flat reference upper bound.
Article: main_krylov, apG:flat. -/
theorem norm_reference_flat_response_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hflat : ∀ i : Fin (referenceAtomCount A hA g), cgEnergy A g i.val = c)
    (hN : 2 ≤ referenceAtomCount A hA g)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ)
    (hf : IsSymmetricForm f)
    (hd : ∀ x, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ 2) :
    ‖referenceCubicResponse A hA g f‖ ≤
      10 * c * referenceAtomCount A hA g * Real.logb 2 (4 * referenceAtomCount A hA g) := by
  have hc := (flat_cg_energy_pos A hA g c hflat (by omega)).le
  let T := symmetricCubicOfMultilinear f hf
  have hT : ∀ x, ‖x‖ = 1 → |T.form x x x| ≤ 2 := by
    intro x hx
    change |cubicCurried f x x x| ≤ 2
    rw [cubicCurried_apply]
    convert hd x hx using 1
    congr 2
    ext i
    fin_cases i <;> rfl
  rw [reference_flat_response A hA g c hflat hc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  have hb := norm_flatForwardResponse_le
    (fun i : Fin (referenceAtomCount A hA g) => canonicalCGUnitStep A g i.val)
    (canonicalCG_frame A hA g) T hT hN
  rw [cubicUncurried_symmetricCubic f hf] at hb
  have hm := mul_le_mul_of_nonneg_left hb hc
  convert hm using 1
  ring

/-- Both printed flat-profile tensor bounds hold for the genuine attained
reference amplification and its genuine nuclear maximum.
Article: main_krylov, apG:flat. -/
theorem reference_flat_tensor_amplification [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hflat : ∀ i : Fin (referenceAtomCount A hA g), cgEnergy A g i.val = c)
    (hN : 2 ≤ referenceAtomCount A hA g) :
    ∃ Γ : ℝ≥0,
      IsGreatest ((fun u : EuclideanSpace ℝ (Fin n) =>
        2 * ‖tensorSymmetrization (referenceCubicTarget A hA g u)‖₊) '' {u | ‖u‖ = 1}) Γ ∧
      IsGreatest ((fun f : ContinuousMultilinearMap ℝ
          (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ => ‖referenceCubicResponse A hA g f‖) ''
        {f | IsSymmetricForm f ∧ ∀ x, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ 2}) (Γ : ℝ) ∧
      (Real.sqrt 3 / 2) * c * (referenceAtomCount A hA g - 1 : ℕ) ≤ Γ ∧
      (Γ : ℝ) ≤ 10 * c * referenceAtomCount A hA g * Real.logb 2 (4 * referenceAtomCount A hA g) := by
  obtain ⟨Γ, hΓ, hresp, _, _⟩ := reference_cubic_amplification A hA g hN
  refine ⟨Γ, hΓ, hresp, ?_, ?_⟩
  · have hc := (flat_cg_energy_pos A hA g c hflat (by omega)).le
    obtain ⟨T, hd, hb⟩ := flat_forward_lower_witness
      (fun i : Fin (referenceAtomCount A hA g) => canonicalCGUnitStep A g i.val)
      (canonicalCG_frame A hA g) hN
    have hmem : ‖referenceCubicResponse A hA g (cubicUncurried T)‖ ≤ (Γ : ℝ) :=
      hresp.2 ⟨cubicUncurried T, ⟨cubicUncurried_symmetric T, cubicUncurried_diagonal_bound T hd⟩, rfl⟩
    rw [reference_flat_response A hA g c hflat hc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] at hmem
    have hm := (mul_le_mul_of_nonneg_left hb hc).trans hmem
    convert hm using 1
    ring
  · obtain ⟨f, ⟨hf, hd⟩, hmax⟩ := hresp.1
    rw [← hmax]
    exact norm_reference_flat_response_le A hA g c hflat hN f hf hd

end
end krylov.Tensor
