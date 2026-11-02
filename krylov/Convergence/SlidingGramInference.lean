import krylov.Convergence.WindowModelBounds

/-!
Article: main_krylov, thm:G, independence-free sliding full conjugacy.
Use: measured triangular conjugacy and vanishing actual secant errors force
the normalized step Gram matrix to converge to the identity. Full-window
independence and inverse conditioning are conclusions, not assumptions.
Source: the exact observed conjugacy equations and the real C-star Gram
identity in the genuine Euclidean spectral matrix norm.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ} {α : Type*} {l : Filter α}

/-- Real triangular observed conjugacy forces the unit-step Gram error to
be small even when independence has not yet been proved. -/
theorem conjugate_window_gram_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin n → E) (hs : ∀ i,‖s i‖=1) {ε : ℝ} (hε : 0≤ε)
    (herr : ∀ i,‖y i-s i‖≤ε)
    (hconj : ∀ i j,i<j → inner ℝ (y i) (s j)=0) :
    ‖crossGram s s-1‖≤n*ε := by
  apply (krylov.LinearAlgebra.spectral_le_hsNorm _).trans
  apply krylov.LinearAlgebra.hsNorm_le_dimension _ hε
  intro i j
  by_cases hij : i=j
  · subst j
    simpa only [Matrix.sub_apply,crossGram,Matrix.one_apply_eq,real_inner_self_eq_norm_sq,
      hs,one_pow,sub_self,abs_zero] using hε
  · have hupper (a b : Fin n) (hab : a<b) : |inner ℝ (s a) (s b)|≤ε := by
      have he : inner ℝ (s a) (s b)=-(inner ℝ (y a-s a) (s b)) := by
        rw [inner_sub_left,hconj a b hab,zero_sub,neg_neg]
      rw [he,abs_neg]
      have hh := norm_inner_le_norm (𝕜:=ℝ) (y a-s a) (s b)
      rw [hs,mul_one,Real.norm_eq_abs] at hh
      exact hh.trans (herr a)
    simp only [Matrix.sub_apply,crossGram,Matrix.one_apply_ne hij,sub_zero]
    rcases lt_or_gt_of_ne hij with h | h
    · exact hupper i j h
    · rw [real_inner_comm]
      exact hupper j i h

/-- Observed conjugacy of real nonzero steps is preserved by their actual
positive column normalizers. -/
theorem conjugate_window_unit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin n → E) (hconj : ∀ i j,i<j → inner ℝ (y i) (s j)=0)
    (i j : Fin n) (hij : i<j) :
    inner ℝ (unitWindowImages s y i) (unitWindow s j)=0 := by
  simp only [unitWindowImages,unitWindow,rescaleWindow,real_inner_smul_left,
    real_inner_smul_right,hconj i j hij,mul_zero]

/-- The genuine inverse Gram norm is the squared inverse-coordinate norm,
including the totalized singular branch. -/
theorem inverse_gram_norm (V : Matrix (Fin n) (Fin n) ℝ) :
    ‖(Vᵀ*V)⁻¹‖=‖V⁻¹‖^2 := by
  rw [Matrix.mul_inv_rev,←transpose_nonsing_inv]
  simpa only [Matrix.star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial,pow_two] using
    CStarRing.norm_self_mul_star (x:=V⁻¹)

/-- Full physical frames with asymptotically identity Gram matrices become
independent, and their actual inverse norms tend to one. -/
theorem gram_identity_window_conditioning
    (V : α → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hG : Tendsto (fun z=>(V z)ᵀ*V z) l (𝓝 1)) :
    (∀ᶠ z in l,IsUnit (V z).det) ∧Tendsto (fun z=>‖(V z)⁻¹‖) l (𝓝 1) := by
  have hgi : Tendsto (fun z=>((V z)ᵀ*V z)⁻¹) l (𝓝 1) := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse,Units.val_one,Ring.inverse_one,Function.comp_def] using
      (NormedRing.inverse_continuousAt (1:(Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ˣ)).tendsto.comp hG
  have hgu : ∀ᶠ z in l,IsUnit ((V z)ᵀ*V z).det :=
    (hG.eventually (Units.isOpen.mem_nhds isUnit_one)).mono fun z hz=>
      (Matrix.isUnit_iff_isUnit_det _).mp hz
  have hunit : ∀ᶠ z in l,IsUnit (V z).det := by
    filter_upwards [hgu] with z hz
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    apply isUnit_iff_ne_zero.mp hz
    rw [det_mul,det_transpose,hzero,mul_zero]
  have hn := hgi.norm.sqrt
  have he (z : α) : Real.sqrt ‖((V z)ᵀ*V z)⁻¹‖=‖(V z)⁻¹‖ := by
    rw [inverse_gram_norm,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  refine ⟨hunit,?_⟩
  simpa only [he,norm_one,Real.sqrt_one] using hn

end
end krylov.Convergence
