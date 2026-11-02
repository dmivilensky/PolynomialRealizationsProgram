import krylov.Tensor.ResponseDuality
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
Article: main_krylov, thm:Hp, compatible response on genuine orthogonal flags.
Use: identify the finite FC tensor contraction with its attained nuclear
maximum and bound it by the actual operator variation budget.
Source: Banach's cubic identity, Bessel's inequality and the proved
projective tensor duality, rather than an assumed tensor norm formula.
-/

namespace krylov.Tensor
noncomputable section
open scoped InnerProductSpace BigOperators TensorProduct NNReal
variable {ι κ E : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual orthogonal flag component of a vector.
Article: main_krylov, thm:Hp. -/
def flagComponent (e : ι → E) (I : Finset ι) (u : E) : E :=
  ∑ i ∈ I, inner ℝ (e i) u • e i

omit [Fintype ι] [DecidableEq ι] in
/-- Orthogonal flag truncation is contractive, even when the family is incomplete.
Article: main_krylov, thm:Hp.
Proof: compute its squared norm by orthonormality and apply Bessel. -/
theorem norm_flagComponent_le (e : ι → E) (he : Orthonormal ℝ e)
    (I : Finset ι) (u : E) : ‖flagComponent e I u‖ ≤ ‖u‖ := by
  have hn : ‖flagComponent e I u‖ ^ 2 = ∑ i ∈ I, ‖inner ℝ (e i) u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    unfold flagComponent
    rw [he.inner_sum]
    simp only [conj_trivial, Real.norm_eq_abs, sq_abs, ← pow_two]
  have hb := he.sum_inner_products_le (s := I) u
  nlinarith [norm_nonneg (flagComponent e I u), norm_nonneg u]

/-- The actual FC compatible cubic response, with its finite old flags.
Article: main_krylov, thm:Hp. -/
def flagResponse (e : ι → E) (I : κ → Finset ι) (ξ v : κ → E)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) : E :=
  ∑ l, ∑ i ∈ I l, f ![e i, ξ l, v l] • e i

omit [Fintype ι] [DecidableEq ι] in
/-- Pairing the finite response contracts its first slot with the true flag component.
Article: main_krylov, thm:Hp.
Proof: finite linearity and the real inner-product symmetry. -/
theorem inner_flagResponse (e : ι → E) (I : κ → Finset ι) (ξ v : κ → E)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (u : E) :
    inner ℝ u (flagResponse e I ξ v f) =
      ∑ l, cubicCurried f (flagComponent e (I l) u) (ξ l) (v l) := by
  simp only [flagResponse, flagComponent, inner_sum, inner_smul_right,
    map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, cubicCurried_apply]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (e i) u]
  ring

variable [FiniteDimensional ℝ E]

omit [Fintype ι] [DecidableEq ι] in
/-- Every genuine compatible response obeys the independent operator budget.
Article: main_krylov, thm:Hp, Gamma_T ≤ Gamma_op.
Proof: pair with the normalized actual output, use Banach's mixed bound,
then contract the true old flags by Bessel's inequality. -/
theorem norm_flagResponse_le (e : ι → E) (he : Orthonormal ℝ e)
    (I : κ → Finset ι) (ξ v : κ → E)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hf : IsSymmetricForm f) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ x : E, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ C) :
    ‖flagResponse e I ξ v f‖ ≤ ∑ l, C * ‖ξ l‖ * ‖v l‖ := by
  have hp (u : E) (hu : ‖u‖ = 1) :
      inner ℝ u (flagResponse e I ξ v f) ≤ ∑ l, C * ‖ξ l‖ * ‖v l‖ := by
    rw [inner_flagResponse]
    apply Finset.sum_le_sum
    intro l _
    have hn := (symmetric_cubic_norm_le_iff f hf hC).mpr hd
    have hb := (le_abs_self (f ![flagComponent e (I l) u, ξ l, v l])).trans
      (f.le_opNorm ![flagComponent e (I l) u, ξ l, v l])
    simp only [Fin.prod_univ_three] at hb
    rw [cubicCurried_apply]
    have hc : ‖flagComponent e (I l) u‖ ≤ 1 := (norm_flagComponent_le e he _ u).trans_eq hu
    calc
      _ ≤ ‖f‖ * (‖flagComponent e (I l) u‖ * ‖ξ l‖ * ‖v l‖) := hb
      _ ≤ C * (1 * ‖ξ l‖ * ‖v l‖) := by gcongr
      _ = _ := by ring
  by_cases hz : flagResponse e I ξ v f = 0
  · rw [hz, norm_zero]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (mul_nonneg hC (norm_nonneg _)) (norm_nonneg _))
  · have hb := hp (NormedSpace.normalize (flagResponse e I ξ v f)) (NormedSpace.norm_normalize hz)
    have hi : inner ℝ (NormedSpace.normalize (flagResponse e I ξ v f))
        (flagResponse e I ξ v f) = ‖flagResponse e I ξ v f‖ := by
      simp only [NormedSpace.normalize, inner_smul_left, conj_trivial,
        real_inner_self_eq_norm_sq]
      field_simp
    rwa [hi] at hb

/-- The genuine symmetrized rank-one target of the FC flag response.
Article: main_krylov, thm:Hp. -/
def flagResponseTensor (e : ι → E) (I : κ → Finset ι) (ξ v : κ → E) (u : E) :
    ⨂[ℝ] _ : Fin 3, E :=
  ∑ l, ∑ i ∈ I l, inner ℝ u (e i) • PiTensorProduct.tprod ℝ ![e i, ξ l, v l]

omit [FiniteDimensional ℝ E] in
/-- The exact source flag response is an instance of the actual finite tensor response.
Article: main_krylov, thm:Hp. Proof: include its actual finite flag indicators. -/
theorem flagResponse_eq_cubicResponse (e : ι → E) (I : κ → Finset ι) (ξ v : κ → E)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) :
    flagResponse e I ξ v f = cubicResponse
      (fun p : κ × ι => if p.2 ∈ I p.1 then e p.2 else 0)
      (fun p => e p.2) (fun p => ξ p.1) (fun p => v p.1) f := by
  unfold flagResponse cubicResponse
  rw [Fintype.sum_prod_type]
  simp only [smul_ite, smul_zero, ← Finset.sum_filter]
  simp

omit [FiniteDimensional ℝ E] in
/-- The target dictionary uses the same actual finite flag indicators.
Article: main_krylov, thm:Hp. Proof: expand the true tensor sum. -/
theorem flagResponseTensor_eq_responseTensor (e : ι → E) (I : κ → Finset ι) (ξ v : κ → E) (u : E) :
    flagResponseTensor e I ξ v u = responseTensor
      (fun p : κ × ι => if p.2 ∈ I p.1 then e p.2 else 0)
      (fun p => e p.2) (fun p => ξ p.1) (fun p => v p.1) u := by
  unfold flagResponseTensor responseTensor
  rw [Fintype.sum_prod_type]
  simp only [apply_ite (inner ℝ u), inner_zero_right, ite_smul, zero_smul, ← Finset.sum_filter]
  simp

/-- The printed compatible FC amplification is the attained directional nuclear maximum.
Article: main_krylov, thm:Hp, exact equality and Gamma_T ≤ Gamma_op.
Proof: instantiate genuine cubic response duality with the actual finite
old flags, then bound an attaining tensor by the proved operator estimate. -/
theorem flagResponse_nuclear_amplification [Nontrivial E]
    (e : ι → E) (he : Orthonormal ℝ e) (I : κ → Finset ι) (ξ v : κ → E) :
    ∃ A : ℝ≥0,
      IsGreatest ((fun u : E => 2 * ‖tensorSymmetrization (flagResponseTensor e I ξ v u)‖₊) ''
        {u : E | ‖u‖ = 1}) A ∧
      IsGreatest ((fun f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ =>
        ‖flagResponse e I ξ v f‖) ''
          {f | IsSymmetricForm f ∧ ∀ x : E, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ 2}) (A : ℝ) ∧
      (A : ℝ) ≤ ∑ l, 2 * ‖ξ l‖ * ‖v l‖ := by
  obtain ⟨A, hA, hB⟩ := cubicResponse_nuclear_amplification
    (fun p : κ × ι => if p.2 ∈ I p.1 then e p.2 else 0)
    (fun p => e p.2) (fun p => ξ p.1) (fun p => v p.1) 2
  simp only [← flagResponse_eq_cubicResponse, ← flagResponseTensor_eq_responseTensor] at hA hB
  refine ⟨A, hA, hB, ?_⟩
  obtain ⟨f, ⟨hf, hd⟩, hmax⟩ := hB.1
  rw [← hmax]
  exact norm_flagResponse_le e he I ξ v f hf (by norm_num) hd

end
end krylov.Tensor
