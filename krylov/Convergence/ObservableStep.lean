import krylov.Convergence.ObservableFrame

/-!
Article: main_krylov, apG:Dunif, uniform FC staircase induction.
Use: extend the true normalized residual bound by one actually conjugate
line step without dividing by its length or a reference step energy.
Source: the symmetric secant identity and Cauchy--Schwarz. These are
finite estimates for real observations, independent of asymptotic rank.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- One true symmetric observed secant and one conjugate line step
increase an old normalized gradient pairing by at most twice the local
operator variation bound times the new length. Article: apG:Dunif. -/
theorem observable_staircase_increment (s t g : E) (A B : E →L[ℝ] E)
    (hs : s≠0) (hA : A.toLinearMap.IsSymmetric) {epsilon : ℝ}
    (ha : ‖A-ContinuousLinearMap.id ℝ E‖≤epsilon)
    (hb : ‖B-ContinuousLinearMap.id ℝ E‖≤epsilon)
    (hc : inner ℝ (A s) t=0) :
    |inner ℝ (‖s‖⁻¹ • s) (g+B t)|≤
      |inner ℝ (‖s‖⁻¹ • s) g|+2*epsilon*‖t‖ := by
  have hd : ‖B-A‖≤2*epsilon := by
    have hh := norm_sub_le_norm_sub_add_norm_sub B (ContinuousLinearMap.id ℝ E) A
    rw [norm_sub_rev (ContinuousLinearMap.id ℝ E) A] at hh
    exact hh.trans (by linarith only [ha,hb])
  have hsym : inner ℝ (A s) t=inner ℝ s (A t) := hA s t
  have he : inner ℝ s (B t)=inner ℝ s ((B-A) t) := by
    rw [_root_.sub_apply,inner_sub_right,←hsym,hc,sub_zero]
  have hunit : ‖‖s‖⁻¹ • s‖=1 := norm_smul_inv_norm hs
  have hi : |inner ℝ (‖s‖⁻¹ • s) (B t)|≤2*epsilon*‖t‖ := by
    rw [real_inner_smul_left,he,←real_inner_smul_left]
    have hh := norm_inner_le_norm (𝕜:=ℝ) (‖s‖⁻¹ • s) ((B-A) t)
    rw [Real.norm_eq_abs,hunit,one_mul] at hh
    exact hh.trans (((B-A).le_opNorm t).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg t)))
  rw [inner_add_right]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hi)

/-- Pairwise measured angular bounds give a true spectral Gram bound,
including the empty window. Article: apG:Dunif, normalized Gram induction. -/
theorem observable_gram_angular (s : Fin p → E) (hs : ∀ i,‖s i‖=1)
    {delta : ℝ} (hd : 0≤delta)
    (hpair : ∀ i j,i≠j → |inner ℝ (s i) (s j)|≤delta) :
    ‖crossGram s s-1‖≤p*delta := by
  apply (spectral_le_hsNorm _).trans
  apply hsNorm_le_dimension _ hd
  intro i j
  by_cases hij : i=j
  · subst j
    simpa only [Matrix.sub_apply,crossGram,Matrix.one_apply_eq,real_inner_self_eq_norm_sq,
      hs,one_pow,sub_self,abs_zero] using hd
  · simpa only [Matrix.sub_apply,crossGram,Matrix.one_apply_ne hij,sub_zero] using hpair i j hij

/-- Every genuine cross-Gram error is bounded by the real relative pair
errors; chronological storage order is immaterial.
Article: main_krylov, apG:Dunif, actual coefficient solve. -/
theorem observable_crossGram_error (s y : Fin p → E) (hs : ∀ i,‖s i‖=1)
    {epsilon : ℝ} (he : 0≤epsilon) (hy : ∀ i,‖y i-s i‖≤epsilon) :
    ‖crossGram y s-crossGram s s‖≤p*epsilon := by
  apply (spectral_le_hsNorm _).trans
  apply hsNorm_le_dimension _ he
  intro i j
  have hh := norm_inner_le_norm (𝕜:=ℝ) (y i-s i) (s j)
  rw [Real.norm_eq_abs,hs j,mul_one,inner_sub_left] at hh
  exact hh.trans (hy i)

/-- A genuine normalized observed cross-Gram near its true Gram has a
real inverse on a derived domain. This works for either storage order.
Article: main_krylov, apG:Dunif. -/
theorem observable_crossGram_domain (s y : Fin p → E) (hs : ∀ i,‖s i‖=1)
    {delta epsilon : ℝ} (he : 0≤epsilon)
    (hg : ‖crossGram s s-1‖≤delta) (hy : ∀ i,‖y i-s i‖≤epsilon)
    (hsmall : delta+p*epsilon≤1/4) :
    IsUnit (crossGram y s).det ∧ ‖(crossGram y s)⁻¹‖≤4/3 := by
  have hh := norm_add_le (crossGram y s-crossGram s s) (crossGram s s-1)
  rw [sub_add_sub_cancel] at hh
  have hn : ‖crossGram y s-1‖≤1/4 :=
    hh.trans (by linarith only [observable_crossGram_error s y hs he hy,hg,hsmall])
  have hi (c : Fin p → ℝ) : 1*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ ((1:Matrix (Fin p) (Fin p) ℝ)*ᵥc) := by
    rw [observable_identity_form,one_mul]
  have hc (c : Fin p → ℝ) : (3/4:ℝ)*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ (crossGram y s*ᵥc) := by
    have hz := krylov.XR.coefficient_coercivity_of_error (crossGram y s) 1 1 (1/4) hi hn c
    linarith
  have hh := krylov.XR.coefficient_inverse_of_coercivity _ (3/4) (by norm_num) hc
  exact ⟨hh.1,hh.2.trans_eq (by norm_num)⟩

end
end krylov.Convergence
