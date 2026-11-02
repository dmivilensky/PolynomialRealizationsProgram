import jacobi.Analytic.ReferenceNormBounds
import jacobi.Analysis.GammaUniform

/-!
Article: jacobi, Lemma C.1.
The printed normalized Gamma norm is exactly Euler's actual Gamma
approximant times two elementary correction factors. All denominators
and complex-power branches are justified on the original half-plane.
Use: ReferenceNormAsymptotic obtains the exact uniform leading constant.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual complex Gamma recurrence evaluates the genuine finite positive-real-part rising product.
Use: gammaSeq_ratio_complex identifies the true Euler approximation with the printed Gamma quotient.
Article: jacobi, Lemma C.1.
Source: Euler's Gamma recurrence, mathlib Gamma.Basic.
Proof: induction on the original product length applies the genuine nonzero-argument Gamma recurrence at every step. -/
theorem gamma_product_complex {s:ℂ} (hs:0<s.re) (n:ℕ) :
    Complex.Gamma (s+n)=Complex.Gamma s*∏ j∈Finset.range n,(s+j) := by
  -- Each positive-real-part step appends exactly one genuine rising Gamma factor.
  induction n with
  | zero=>simp
  | succ n ih=>
    have hp:s+(n:ℂ)≠0:=by
      apply ne_of_apply_ne Complex.re
      simp only [Complex.add_re,Complex.natCast_re,Complex.zero_re]
      positivity
    rw [Nat.cast_add,Nat.cast_one,← add_assoc,Complex.Gamma_add_one _ hp,ih,Finset.prod_range_succ]
    ring

/-- The actual complex Euler sequence has exactly the original Gamma quotient at each degree.
Use: scaledNorming_euler_factorization connects the proven uniform Euler limit to the genuine printed reference norm.
Article: jacobi, Lemma C.1.
Proof: evaluate its finite denominator product by the genuine Gamma recurrence and its factorial by Gamma(n+1). Every original Gamma denominator avoids all poles in the positive-real-part half-plane. -/
theorem gammaSeq_ratio_complex {s:ℂ} (hs:0<s.re) (n:ℕ) :
    Complex.GammaSeq s n=Complex.Gamma s*(n:ℂ)^s*Complex.Gamma ((n:ℂ)+1)/
      (((n:ℂ)+s)*Complex.Gamma ((n:ℂ)+s)) := by
  -- The exact rising product is retained until the actual Gamma quotient has been established.
  have hsn:0<(s+(n:ℂ)).re:=by
    simp only [Complex.add_re,Complex.natCast_re]
    positivity
  have hG:=gamma_product_complex hs (n+1)
  rw [Nat.cast_add,Nat.cast_one,← add_assoc,Complex.Gamma_add_one _ ((Complex.ne_zero_of_re_pos hsn))] at hG
  have hp:(∏ j∈Finset.range (n+1),(s+(j:ℂ)))≠0:=by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact ne_of_apply_ne Complex.re (show (s+(j:ℂ)).re≠0 by
      simp only [Complex.add_re,Complex.natCast_re]
      positivity)
  rw [Complex.GammaSeq,Complex.Gamma_nat_eq_factorial,add_comm (n:ℂ) s]
  field_simp [hp,Complex.Gamma_ne_zero (gamma_no_pole hs),
    Complex.Gamma_ne_zero (gamma_no_pole hsn),(Complex.ne_zero_of_re_pos hsn)]
  linear_combination (n:ℂ)^s*(n.factorial:ℂ)*hG

/-- The elementary affine-index correction in the actual complex reference norm.
Use: its uniform unit limit is combined with the true Euler Gamma factor.
Article: jacobi, Lemma C.1.
-/
def normAffineFactor (g:ℂ) (n:ℕ) : ℂ := ((n:ℂ)+2*g)/((n:ℂ)+g)

/-- The elementary positive-base power correction in the actual complex reference norm.
Use: its exponent tends uniformly to zero when the original complex orders remain in a compact set.
Article: jacobi, Lemma C.1.
-/
def normPowerFactor (g:ℂ) (n:ℕ) : ℂ :=
  Complex.exp (2*g*(Real.log (1+1/(n:ℝ)):ℂ))

/-- The printed complex-normalized reference norm is exactly its genuine Euler-Gamma factor times the two elementary original-index corrections.
Use: ReferenceNormAsymptotic proves the exact compact-uniform leading constant for the original norm integral.
Article: jacobi, Lemma C.1.
Proof: the true Gamma product gives the Euler factor. On the positive real axis the exact complex-power quotient equals the exponential of the real logarithm. Cancel only the proved nonzero original Gamma, affine and positive-base factors. -/
theorem scaledNorming_euler_factorization {a:ℂ} (ha:0<(gamma a).re) {n:ℕ} (hn:0<n) :
    scaledNorming a n/normConstant a=
      (Complex.GammaSeq (2*gamma a) n/Complex.Gamma (2*gamma a))*
        normAffineFactor (gamma a) n*normPowerFactor (gamma a) n := by
  -- The factorization concerns the actual printed Gamma norm and preserves its complex phase.
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn
  have hnC:(n:ℂ)≠0:=by exact_mod_cast hn.ne'
  have hg2:0<(2*gamma a).re:=by norm_num; linarith
  have hna:0<((n:ℂ)+gamma a).re:=by simp only [Complex.add_re,Complex.natCast_re]; positivity
  have hn2:0<((n:ℂ)+2*gamma a).re:=by simp only [Complex.add_re,Complex.natCast_re]; positivity
  have hp:normPowerFactor (gamma a) n=((n:ℂ)+1)^(2*gamma a)/(n:ℂ)^(2*gamma a):=by
    rw [normPowerFactor]
    have hr:1+1/(n:ℝ)=((n:ℝ)+1)/(n:ℝ):=by field_simp
    rw [hr,Complex.ofReal_log (by positivity),mul_comm (2*gamma a),
      ← Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos (by positivity) hnR).ne'),
      Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (by positivity) hnR.le]
    push_cast
    rfl
  rw [gammaSeq_ratio_complex hg2,hp]
  unfold scaledNorming norming normAffineFactor
  push_cast
  simp only [mul_comm (2:ℂ) (gamma a)] at *
  have hG0:Complex.Gamma (gamma a*2)≠0:=Complex.Gamma_ne_zero_of_re_pos hg2
  have hG1:Complex.Gamma ((n:ℂ)+gamma a*2)≠0:=Complex.Gamma_ne_zero_of_re_pos hn2
  have hcp:(n:ℂ)^(gamma a*2)≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
  field_simp [hG0,hG1,hcp,normConstant_ne_zero ha,Complex.Gamma_ne_zero (gamma_no_pole hg2),
    Complex.Gamma_ne_zero (gamma_no_pole hn2),(Complex.ne_zero_of_re_pos hna),
    (Complex.ne_zero_of_re_pos hn2),Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)]

/-- The true affine correction differs from one by at most B/n uniformly over the original bounded positive-real-part orders.
Use: the exact normalized reference norm asymptotic retains every original affine index offset.
Article: jacobi, Lemma C.1.
Proof: its exact difference is gamma/(n+gamma). The real part of its denominator is at least n, which bounds its actual complex norm away from zero. -/
theorem normAffineFactor_error {g:ℂ} (hg:0<g.re) {B:ℝ} (hB:‖g‖≤B) {n:ℕ} (hn:0<n) :
    ‖normAffineFactor g n-1‖≤B/(n:ℝ) := by
  -- Positive real part supplies a genuine lower denominator bound, rather than a magnitude asymptotic assumption.
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn
  have hd:(n:ℝ)≤‖(n:ℂ)+g‖:=by
    have h:=Complex.re_le_norm ((n:ℂ)+g)
    simp only [Complex.add_re,Complex.natCast_re] at h
    linarith
  have hnz:(n:ℂ)+g≠0:=norm_pos_iff.mp (hnR.trans_le hd)
  have he:normAffineFactor g n-1=g/((n:ℂ)+g):=by
    unfold normAffineFactor
    field_simp
    ring
  rw [he,norm_div]
  exact (div_le_div_of_nonneg_right hB (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left ((norm_nonneg g).trans hB) hnR hd)

end
end jacobi.ComplexReference
