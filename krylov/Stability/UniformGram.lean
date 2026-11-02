import krylov.Methods.ProjectedModel
import krylov.LinearAlgebra.MatrixNormBounds
import Mathlib.Analysis.Normed.Ring.Units

/-!
Article: main_krylov, apB:lem:UAsteps and eq:weighted-flags, uniform Gram conditioning.
Use: control the actual Gram inverse using pairwise normalized angles only,
with constants depending on the number of columns and no smallest step energy.
Source: genuine spectral-versus-Frobenius norm comparison and the standard
Neumann geometric-series inverse in mathlib.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- The actual Gram deviation of almost orthonormal columns is at most their number times their largest angle.
Use: true FC angle estimates imply spectral Gram conditioning without dividing by physical step lengths.
Article: main_krylov, apB:lem:UAsteps, G=I+O(δ).
Proof: diagonal deviations vanish because the actual columns are unit; each
other actual entry is bounded by the angle hypothesis. The proved genuine
Frobenius comparison supplies the dimension factor in the spectral norm. -/
theorem unitGram_deviation (t : Fin p → E) (ht : ∀ i, ‖t i‖=1) {η : ℝ}
    (hη : 0≤η) (ha : ∀ i j, i≠j → |inner ℝ (t i) (t j)|≤η) :
    ‖crossGram t t-1‖≤(p : ℝ)*η := by
  -- Work with the real entry error before applying any spectral inverse estimate.
  apply (spectral_le_hsNorm _).trans (hsNorm_le_dimension _ hη ?_)
  intro i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.sub_apply,crossGram,one_apply_eq,real_inner_self_eq_norm_sq,ht,one_pow,sub_self,abs_zero]
    exact hη
  · simpa only [Matrix.sub_apply,crossGram,one_apply_ne hij,sub_zero] using ha i j hij

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A genuine real spectral matrix within one half of the identity has inverse norm at most two and linear inverse deviation.
Use: uniform FC Gram and model inverse control needs no reference-dependent determinant lower bound.
Article: main_krylov, apB:lem:UAsteps and eq:weighted-flags.
Source: the standard Neumann geometric series, mathlib NormedRing.inverse_one_sub.
Proof: the true Neumann series supplies the actual inverse domain and its
norm bound; multiply M⁻¹ by the real deviation I−M for the inverse error.
The empty coefficient space is handled separately. -/
theorem near_identity_inverse (M : Matrix (Fin p) (Fin p) ℝ) (hM : ‖M-1‖≤(1/2 : ℝ)) :
    IsUnit M.det ∧ ‖M⁻¹‖≤2 ∧ ‖M⁻¹-1‖≤2*‖M-1‖ := by
  -- Even the inverse domain is proved from the normalized spectral deviation.
  by_cases hp : p=0
  · subst p
    have hz : M=0 := Subsingleton.elim _ _
    have ho : (1 : Matrix (Fin 0) (Fin 0) ℝ)=0 := Subsingleton.elim _ _
    simp [hz,ho]
  have : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hp)
  have hnorm : ‖1-M‖=‖M-1‖ := norm_sub_rev _ _
  have hsmall : ‖1-M‖<1 := by rw [hnorm]; linarith
  have hu : IsUnit M := by simpa only [Units.val_oneSub,sub_sub_cancel] using (Units.oneSub (1-M) hsmall).isUnit
  have hdet := (Matrix.isUnit_iff_isUnit_det M).mp hu
  have he : M⁻¹=∑' j : ℕ, (1-M)^j := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    simpa only [sub_sub_cancel] using (geom_series_eq_inverse (1-M) hsmall).symm
  have hi : ‖M⁻¹‖≤2 := by
    rw [he]
    have hs := tsum_geometric_le_of_norm_lt_one (1-M) hsmall
    have hb : (1-‖1-M‖)⁻¹≤2 := inv_le_of_inv_le₀ (by norm_num) (by rw [hnorm]; linarith)
    simp only [norm_one,sub_self,zero_add] at hs
    exact hs.trans hb
  refine ⟨hdet,hi,?_⟩
  have herr : M⁻¹-1=M⁻¹*(1-M) := by rw [mul_sub,Matrix.mul_one,Matrix.nonsing_inv_mul _ hdet]
  rw [herr]
  exact (norm_mul_le _ _).trans (by rw [hnorm]; exact mul_le_mul_of_nonneg_right hi (norm_nonneg _))

end
end krylov.Stability
