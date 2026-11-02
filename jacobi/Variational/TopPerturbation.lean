import jacobi.Variational.TopGap

/-!
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
The leading eigenvalue of a positive compact operator has a first-order
term given by its unit ground vector, with the printed quadratic remainder.
The proof uses an orthogonal decomposition and square completion; it needs
no analytic perturbation theorem or differentiable eigenvector choice.
Source: the elementary spectral-gap argument in jacobi.
Use: controls the diagonal and cross terms in the spectral-gap expansion.
-/
namespace jacobi.Variational
noncomputable section
open Real chebyshev2.Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The operator norm bounds every signed bilinear matrix element.
Use: controls the diagonal and cross terms in the spectral-gap expansion.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Source: the Hilbert-space Cauchy--Schwarz inequality.
Proof: bound the inner product by the product of vector norms and apply the operator norm. -/
theorem operator_pairing_bound (B : E →L[ℝ] E) {C : ℝ} (hC : ‖B‖≤C) (x y : E) :
    |inner ℝ x (B y)|≤C*‖x‖*‖y‖ := by
  calc
    _ ≤ ‖x‖*‖B y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖*(C*‖y‖) := mul_le_mul_of_nonneg_left
      ((B.le_opNorm y).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring

/-- A simple gapped top vector controls every perturbed unit Rayleigh quotient.
Use: the upper estimate in the actual leading-eigenvalue first variation.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Proof: decompose f=a e+h, h perpendicular to e. The gap bounds the unperturbed
complement, all perturbation terms use its norm bound, and completing the
square in norm(h) gives the quadratic remainder. -/
theorem gapped_rayleigh_upper {K B : E →L[ℝ] E}
    (hK : K.IsSymmetric) (hB : B.IsSymmetric) {e : E} (he : ‖e‖=1)
    {μ ε C : ℝ} (hε : 0<ε) (hC : ‖B‖≤C) (hsmall : C≤ε/4)
    (hKe : K e=μ • e)
    (hgap : ∀ h : E, inner ℝ e h=0 → inner ℝ h (K h)≤(μ-ε)*‖h‖^2)
    (f : E) (hf : ‖f‖=1) :
    inner ℝ f ((K+B) f)≤μ+inner ℝ e (B e)+2*C^2/ε := by
  -- Orthogonal projection isolates the sole direction without a spectral gap.
  let a := inner ℝ e f
  let h := f-a • e
  have heh : inner ℝ e h=0 := by
    dsimp [h,a]
    rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,he]
    ring
  have hpy : a^2+‖h‖^2=1 := by
    dsimp only [h]
    rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,he,hf,Real.norm_eq_abs]
    dsimp only [a]
    rw [mul_one,sq_abs]
    rw [real_inner_comm f e]
    ring
  have hrep : f=a • e+h := by dsimp only [h]; abel
  have habs : |a|≤1 := by nlinarith [sq_abs a,sq_nonneg ‖h‖,abs_nonneg a]
  have hKcross : inner ℝ e (K h)=0 := by
    have hs : inner ℝ (K e) h=inner ℝ e (K h) := hK e h
    rw [← hs,hKe,real_inner_smul_left,heh,mul_zero]
  have hhe : inner ℝ h e=0 := (real_inner_comm h e).symm.trans heh
  have hBcross : inner ℝ h (B e)=inner ℝ e (B h) := by
    have hs : inner ℝ (B e) h=inner ℝ e (B h) := hB e h
    exact (real_inner_comm h (B e)).symm.trans hs
  have hex : inner ℝ f ((K+B) f)=a^2*(μ+inner ℝ e (B e))+
      2*a*inner ℝ e (B h)+inner ℝ h (K h)+inner ℝ h (B h) := by
    conv_lhs => rw [hrep]
    simp only [add_apply,map_add,map_smul,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right,hKe,hhe,hKcross,hBcross,
      real_inner_self_eq_norm_sq,he]
    ring
  have hC0 : 0≤C := (norm_nonneg B).trans hC
  have hdiag := operator_pairing_bound B hC e e
  simp only [he,mul_one] at hdiag
  have hcross := operator_pairing_bound B hC e h
  simp only [he,mul_one] at hcross
  have hlast := operator_pairing_bound B hC h h
  have hcross' : 2*a*inner ℝ e (B h)≤2*C*‖h‖ := by
    calc
      _ ≤ |2*a*inner ℝ e (B h)| := le_abs_self _
      _ = 2*|a| * |inner ℝ e (B h)| := by rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
      _ ≤ 2*1*(C*‖h‖) := mul_le_mul
        (mul_le_mul_of_nonneg_left habs (by norm_num)) hcross (abs_nonneg _) (by positivity)
      _ = _ := by ring
  -- Square completion gives the printed constant, using epsilon-2C >= epsilon/2.
  have hd := (abs_le.mp hdiag).1
  have hl := (le_abs_self _).trans hlast
  have hg := hgap h heh
  have hrem : 0≤(ε*‖h‖-2*C)^2 := sq_nonneg _
  have hbound : inner ℝ f ((K+B) f)-μ-inner ℝ e (B e)≤2*C^2/ε := by
    rw [hex]
    apply (le_div_iff₀ hε).mpr
    have hδ : 0≤(C+inner ℝ e (B e))*‖h‖^2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hs : 0≤(ε/2-2*C)*‖h‖^2 := mul_nonneg (by linarith) (sq_nonneg _)
    have hquad : a^2*(μ+inner ℝ e (B e))+2*a*inner ℝ e (B h)+
        inner ℝ h (K h)+inner ℝ h (B h)≤
        μ+inner ℝ e (B e)+2*C*‖h‖-(ε/2)*‖h‖^2 := by
      nlinarith [congrArg (fun r : ℝ => r*(μ+inner ℝ e (B e))) hpy]
    have hm := mul_le_mul_of_nonneg_right hquad hε.le
    nlinarith [hrem]
  linarith

/-- Quantitative first variation of the actual ordered leading eigenvalue.
Use: transfers the abstract gap estimate to signed L1 density perturbations.
Article: jacobi, Appendix D.1 (moment and top-eigenvalue variations).
Proof: the old unit top vector gives the Rayleigh lower bound. Positivity of
that lower bound guarantees an attained perturbed top, to which the proved
unit-vector upper bound applies. -/
theorem top_eigenvalue_expansion {K Z B : E →L[ℝ] E}
    (D : PositiveSpectralData K) (Q : PositiveSpectralData Z) (hZ : Z=K+B)
    (hK : K.IsSymmetric) (hB : B.IsSymmetric)
    {e : E} (he : ‖e‖=1) (hKe : K e=D.eigenvalue 0 • e)
    {ε C : ℝ} (hε : 0<ε) (hεμ : ε≤D.eigenvalue 0)
    (hC : ‖B‖≤C) (hsmall : C≤ε/4)
    (hgap : ∀ h : E, inner ℝ e h=0 → inner ℝ h (K h)≤(D.eigenvalue 0-ε)*‖h‖^2) :
    0≤Q.eigenvalue 0-D.eigenvalue 0-inner ℝ e (B e) ∧
    Q.eigenvalue 0-D.eigenvalue 0-inner ℝ e (B e)≤2*C^2/ε := by
  -- The lower bound also proves that the perturbed operator is nonzero.
  subst Z
  have hl := Q.top_quadratic_bound e
  simp only [add_apply,inner_add_right,hKe,real_inner_smul_right,
    real_inner_self_eq_norm_sq,he,one_pow,mul_one] at hl
  have hb := operator_pairing_bound B hC e e
  simp only [he,mul_one] at hb
  have hq : 0<Q.eigenvalue 0 := by linarith [(abs_le.mp hb).1]
  obtain ⟨_,f,hf,hfQ⟩ := Q.top_attained (hq.trans_le (Q.eigenvalue_le_trace 0))
  have hu := gapped_rayleigh_upper hK hB he hε hC hsmall hKe hgap f hf
  rw [hfQ,real_inner_smul_right,real_inner_self_eq_norm_sq,hf] at hu
  simp only [one_pow,mul_one] at hu
  constructor <;> linarith

end
end jacobi.Variational
