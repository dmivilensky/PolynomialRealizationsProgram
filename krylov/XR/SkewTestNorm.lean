import krylov.XR.RealComplexPositive

/-!
Article: main_krylov, prop:cert, exact spectral meaning of the complex test.
Use: prove the skew-defect criterion from its real quadratic form, using
an attained real operator norm rather than assuming a skew spectral normal
form. Source: finite-dimensional compactness and Cauchy--Schwarz.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
variable {p : ℕ}

/-- Multiplication by i turns a real skew matrix into a Hermitian matrix.
Article: main_krylov, prop:cert. -/
theorem imaginary_skew_isHermitian (K : Matrix (Fin p) (Fin p) ℝ) (hK : Kᵀ= -K) :
    (Complex.I • K.map Complex.ofReal).IsHermitian := by
  change (Complex.I • K.map Complex.ofReal)ᴴ=Complex.I • K.map Complex.ofReal
  ext i j
  have he := congrFun (congrFun hK i) j
  change K j i= -K i j at he
  simp [conjTranspose_apply,he]

/-- The normalized actual skew test is genuinely Hermitian.
Article: main_krylov, prop:cert. -/
theorem normalized_skew_isHermitian (K : Matrix (Fin p) (Fin p) ℝ) (hK : Kᵀ= -K) :
    (1+Complex.I • K.map Complex.ofReal).IsHermitian :=
  Matrix.isHermitian_one.add (imaginary_skew_isHermitian K hK)

/-- A real coordinate square is its genuine Euclidean squared norm.
Article: main_krylov, prop:cert. -/
theorem real_dot_self (x : Fin p → ℝ) :
    x ⬝ᵥ x=‖WithLp.toLp 2 x‖^2 := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] using
    (real_inner_self_eq_norm_sq (WithLp.toLp 2 x))

/-- The real quadratic form of the normalized skew test.
Article: main_krylov, prop:cert. -/
theorem normalized_skew_quadratic_re (K : Matrix (Fin p) (Fin p) ℝ) (hK : Kᵀ= -K)
    (x y : Fin p → ℝ) :
    (star (complexVector x y) ⬝ᵥ ((1+Complex.I • K.map Complex.ofReal)*ᵥ
      complexVector x y)).re=
      ‖WithLp.toLp 2 x‖^2+‖WithLp.toLp 2 y‖^2-2*(x ⬝ᵥ (K*ᵥ y)) := by
  have he : (1 : Matrix (Fin p) (Fin p) ℂ)=(1 : Matrix (Fin p) (Fin p) ℝ).map
      Complex.ofReal := by
    ext i j
    by_cases h : i=j
    · subst j
      simp only [one_apply_eq,map_apply,Complex.ofReal_one]
    · simp only [one_apply_ne h,map_apply,Complex.ofReal_zero]
  rw [he,hermitian_pair_quadratic_re,one_mulVec,one_mulVec,skew_cross_pairing K hK,
    real_dot_self,real_dot_self]
  ring

/-- The canonical Hermitian test passes whenever the actual real skew
operator norm is below one. Article: main_krylov, prop:cert. -/
theorem normalized_skew_posDef_of_norm_lt (K : Matrix (Fin p) (Fin p) ℝ)
    (hK : Kᵀ= -K) (hn : ‖K‖<1) :
    (1+Complex.I • K.map Complex.ofReal).PosDef := by
  have hH := normalized_skew_isHermitian K hK
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hH
  intro z hz
  let x : Fin p → ℝ := fun i=>(z i).re
  let y : Fin p → ℝ := fun i=>(z i).im
  have he : z=complexVector x y := by
    ext i
    exact (Complex.re_add_im (z i)).symm.trans (by simp [complexVector,x,y,mul_comm])
  have hxy : 0<‖WithLp.toLp 2 x‖^2+‖WithLp.toLp 2 y‖^2 := by
    have hne : WithLp.toLp 2 x≠0 ∨ WithLp.toLp 2 y≠0 := by
      by_contra! h
      apply hz
      rw [he]
      have hx : x=0 := by simpa using h.1
      have hy : y=0 := by simpa using h.2
      ext i
      simp [complexVector,hx,hy]
    rcases hne with hx|hy
    · nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hx),sq_nonneg ‖WithLp.toLp 2 y‖]
    · nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hy),sq_nonneg ‖WithLp.toLp 2 x‖]
  have hc : x ⬝ᵥ (K*ᵥ y)≤‖WithLp.toLp 2 x‖*‖K‖*‖WithLp.toLp 2 y‖ := by
    have hc := real_inner_le_norm (WithLp.toLp 2 x) (WithLp.toLp 2 (K*ᵥ y))
    have hm := Matrix.l2_opNorm_mulVec K (WithLp.toLp 2 y)
    change ‖WithLp.toLp 2 (K*ᵥ y)‖≤‖K‖*‖WithLp.toLp 2 y‖ at hm
    have ht := mul_le_mul_of_nonneg_left hm (norm_nonneg (WithLp.toLp 2 x))
    simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial] at hc
    have hc' : x ⬝ᵥ (K*ᵥ y)≤‖WithLp.toLp 2 x‖*‖WithLp.toLp 2 (K*ᵥ y)‖ := by
      simpa only [dotProduct_comm] using hc
    exact hc'.trans (by simpa only [mul_assoc] using ht)
  have hp : 0<(1-‖K‖)*(‖WithLp.toLp 2 x‖^2+‖WithLp.toLp 2 y‖^2) :=
    mul_pos (sub_pos.mpr hn) hxy
  have hq : 0<(star z ⬝ᵥ ((1+Complex.I • K.map Complex.ofReal)*ᵥ z)).re := by
    rw [he,normalized_skew_quadratic_re K hK]
    nlinarith [mul_nonneg (norm_nonneg K)
      (sq_nonneg (‖WithLp.toLp 2 x‖-‖WithLp.toLp 2 y‖))]
  exact Complex.lt_def.mpr ⟨hq,(hH.im_star_dotProduct_mulVec_self z).symm⟩

/-- Positivity forces the true real skew norm below one; the maximizing
real vector supplies the sharp converse. Article: main_krylov, prop:cert. -/
theorem normalized_skew_norm_lt_of_posDef (K : Matrix (Fin p) (Fin p) ℝ)
    (hK : Kᵀ= -K) (hH : (1+Complex.I • K.map Complex.ofReal).PosDef) : ‖K‖<1 := by
  cases p with
  | zero =>
    have he : K=0 := Subsingleton.elim _ _
    simp [he]
  | succ n =>
    obtain ⟨y,hy,hm⟩ := euclidean_operator_norm_attained
      (Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) K)
    rw [Matrix.l2_opNorm_toEuclideanCLM] at hm
    let x := K*ᵥ WithLp.ofLp y
    have hz : complexVector x (WithLp.ofLp y)≠0 := by
      intro hz
      have hz' : y=0 := by
        apply WithLp.ofLp_injective 2
        ext i
        have hi := congrArg Complex.im (congrFun hz i)
        simpa [complexVector] using hi
      simp [hz'] at hy
    have hq := hH.re_dotProduct_pos hz
    change 0<(star (complexVector x (WithLp.ofLp y)) ⬝ᵥ
      ((1+Complex.I • K.map Complex.ofReal)*ᵥ complexVector x (WithLp.ofLp y))).re at hq
    rw [normalized_skew_quadratic_re K hK,hy,one_pow] at hq
    have hx : x ⬝ᵥ (K*ᵥ WithLp.ofLp y)=‖K‖^2 := by
      rw [show K*ᵥ WithLp.ofLp y=x from rfl,real_dot_self]
      exact congrArg (fun t : ℝ=>t^2) hm
    have hxn : ‖WithLp.toLp 2 x‖=‖K‖ := hm
    rw [hx,hxn] at hq
    nlinarith [norm_nonneg K]

/-- Exact sharp equivalence, including the empty window.
Article: main_krylov, prop:cert. -/
theorem normalized_skew_posDef_iff (K : Matrix (Fin p) (Fin p) ℝ) (hK : Kᵀ= -K) :
    (1+Complex.I • K.map Complex.ofReal).PosDef ↔ ‖K‖<1 :=
  ⟨normalized_skew_norm_lt_of_posDef K hK,normalized_skew_posDef_of_norm_lt K hK⟩

end
end krylov.XR
