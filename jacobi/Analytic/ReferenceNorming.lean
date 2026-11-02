import jacobi.Analytic.ReferenceWave
import jacobi.Reference.NormingFormula
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
Article: jacobi, Lemma C.1.
The printed Gamma quotient supplies a holomorphic, zero-free continuation
of every actual real reference norm. The exact real integral formula
already proved in the project fixes all constants in this continuation.
Uniform index bounds and the complex bilinear integral identity are
separate estimates; they are not assumed here.
Use: the community Gamma analyticity and nonvanishing theorems apply to every actual norming factor.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Positive-real-part Gamma arguments avoid every nonpositive integer pole.
Use: the community Gamma analyticity and nonvanishing theorems apply to every actual norming factor.
Article: jacobi, Lemma C.1.
Proof: equality with a nonpositive integer contradicts the strictly positive real part. -/
theorem gamma_no_pole {s : ℂ} (hs : 0<s.re) (n : ℕ) : s≠-(n:ℂ) := by
  intro he
  have hh := congrArg Complex.re he
  simp only [Complex.neg_re,Complex.natCast_re] at hh
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- The actual community Gamma function is analytic at every positive-real-part argument.
Use: proves holomorphy of the printed reference norm quotient.
Article: jacobi, Lemma C.1.
Source: Euler's Gamma integral and analytic continuation, mathlib Gamma.Deriv.
Proof: the community differentiability theorem applies throughout the
open positive half-plane, because all its points avoid the actual Gamma poles. -/
theorem gamma_analytic {s : ℂ} (hs : 0<s.re) : AnalyticAt ℂ Complex.Gamma s := by
  let U : Set ℂ := {z | 0<z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Complex.Gamma U := fun z hz =>
    (Complex.differentiableAt_Gamma z (gamma_no_pole hz)).differentiableWithinAt
  exact hd.analyticOnNhd hU s hs

/-- The literal complex Gamma normalization printed in the reference norm formula.
Use: preserves the original scalar A(gamma) in the continued GL weights.
Article: jacobi, Lemma C.1.
-/
def normConstant (a : ℂ) : ℂ :=
  (2:ℂ)^(1-2*gamma a)*Complex.Gamma (2*gamma a)^2/
    ((Real.pi:ℂ)^(2*gamma a)*Complex.Gamma (gamma a)^2)

/-- The printed Gamma quotient continuing the actual original reference norm.
Use: the analytic GL kernel uses these holomorphic weights, whose real restrictions are the already proved original norm integrals.
Article: jacobi, Lemma C.1.
-/
def norming (a : ℂ) (k : ℕ) : ℂ :=
  normConstant a*Complex.Gamma ((k:ℂ)+1)/(((k:ℂ)+gamma a)*Complex.Gamma ((k:ℂ)+2*gamma a))

/-- The genuine printed normalization is nonzero on the complete positive-exponent half-plane.
Use: the continued reference norms have no artificial zeros.
Article: jacobi, Lemma C.1.
Proof: Gamma has no zeros at positive-real-part arguments and powers of
the nonzero positive constants two and pi are nonzero. -/
theorem normConstant_ne_zero {a : ℂ} (ha : 0<(gamma a).re) : normConstant a≠0 := by
  have h2 : 0<(2*gamma a).re := by norm_num; linarith
  apply div_ne_zero
  · exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
      (pow_ne_zero _ (Complex.Gamma_ne_zero (gamma_no_pole h2)))
  · exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (pow_ne_zero _ (Complex.Gamma_ne_zero (gamma_no_pole ha)))

/-- The actual normalization quotient is analytic along every analytic order curve with positive exponent real part.
Use: all continued norming weights are holomorphic in the original order.
Article: jacobi, Lemma C.1.
Proof: compose the actual Gamma functions with the analytic affine
exponent, and the fixed positive-base powers with their analytic
exponents. The proved nonzero Gamma and power factors justify division. -/
theorem normConstant_comp_analytic {A : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ A p) (ha : 0<(gamma (A p)).re) :
    AnalyticAt ℂ (fun u => normConstant (A u)) p := by
  -- Every denominator here is the literal source normalization, with nonvanishing proved above.
  have hg : AnalyticAt ℂ (fun u => gamma (A u)) p := by unfold gamma; fun_prop
  have h2g : AnalyticAt ℂ (fun u => 2*gamma (A u)) p := analyticAt_const.mul hg
  have h2 : 0<(2*gamma (A p)).re := by norm_num; linarith
  have hG := (gamma_analytic ha).comp (f := fun u => gamma (A u)) hg
  have hG2 := (gamma_analytic h2).comp (f := fun u => 2*gamma (A u)) h2g
  have hpow2 := (analyticAt_const (v := (2:ℂ))).cpow ((analyticAt_const (v := (1:ℂ))).sub h2g)
    (Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num)))
  have hpowpi := (analyticAt_const (v := (Real.pi:ℂ))).cpow h2g
    (Complex.mem_slitPlane_iff.mpr (Or.inl Real.pi_pos))
  exact (hpow2.mul (hG2.pow 2)).div (hpowpi.mul (hG.pow 2))
    (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (pow_ne_zero _ (Complex.Gamma_ne_zero (gamma_no_pole ha))))

/-- Every actual continued reference norm is nonzero on the complete positive-exponent half-plane.
Use: the analytic GL summands divide only by genuinely nonzero original norming weights.
Article: jacobi, Lemma C.1.
Proof: the original Gamma normalization is nonzero; the remaining Gamma
arguments and the affine index factor all have positive real parts. -/
theorem norming_ne_zero {a : ℂ} (ha : 0<(gamma a).re) (k : ℕ) : norming a k≠0 := by
  have hk : 0<((k:ℂ)+1).re := by norm_num; positivity
  have hkg : 0<((k:ℂ)+gamma a).re := by simp only [Complex.add_re,Complex.natCast_re]; positivity
  have hk2g : 0<((k:ℂ)+2*gamma a).re := by norm_num; positivity
  exact div_ne_zero (mul_ne_zero (normConstant_ne_zero ha) (Complex.Gamma_ne_zero (gamma_no_pole hk)))
    (mul_ne_zero (ne_of_apply_ne Complex.re hkg.ne') (Complex.Gamma_ne_zero (gamma_no_pole hk2g)))

/-- The literal continued reference norm is analytic along every analytic complex-order curve in its original half-plane.
Use: supplies the actual holomorphic denominator in Appendix E.1, including every finite index.
Article: jacobi, Lemma C.1.
Proof: compose the true Gamma denominator with the analytic order curve;
its argument and the affine index factor have positive real part, so
the displayed holomorphic quotient has nonzero denominator. -/
theorem norming_comp_analytic {A : ℂ → ℂ} {p : ℂ}
    (hA : AnalyticAt ℂ A p) (ha : 0<(gamma (A p)).re) (k : ℕ) :
    AnalyticAt ℂ (fun u => norming (A u) k) p := by
  have hg : AnalyticAt ℂ (fun u => gamma (A u)) p := by unfold gamma; fun_prop
  have hkg : 0<((k:ℂ)+gamma (A p)).re := by simp only [Complex.add_re,Complex.natCast_re]; positivity
  have hk2g : 0<((k:ℂ)+2*gamma (A p)).re := by norm_num; positivity
  exact ((normConstant_comp_analytic hA ha).mul analyticAt_const).div
    ((analyticAt_const.add hg).mul ((gamma_analytic hk2g).comp (f := fun u => (k:ℂ)+2*gamma (A u))
      (analyticAt_const.add (analyticAt_const.mul hg))))
    (mul_ne_zero (ne_of_apply_ne Complex.re hkg.ne') (Complex.Gamma_ne_zero (gamma_no_pole hk2g)))

/-- The continued normalization scalar agrees exactly with the original real scalar.
Use: identifies the holomorphic reference norm weights with the actual original real norm integrals.
Article: jacobi, Lemma C.1.
Proof: real inclusion commutes with the positive-base powers, Gamma
values and all arithmetic in the original displayed normalization. -/
theorem normConstant_real (a : ℝ) : normConstant (a:ℂ)=(jacobi.Reference.normConstant a:ℂ) := by
  -- Keep the real exponent expressions together so their genuine positive-base power identities apply exactly.
  unfold normConstant jacobi.Reference.normConstant
  rw [gamma_real]
  have h2 : (2:ℂ)*(jacobi.Reference.gamma a:ℂ)=((2* jacobi.Reference.gamma a:ℝ):ℂ) := by push_cast; rfl
  have h1 : (1:ℂ)-2*(jacobi.Reference.gamma a:ℂ)=((1-2* jacobi.Reference.gamma a:ℝ):ℂ) := by push_cast; rfl
  have hp2 := Complex.ofReal_cpow (x := (2:ℝ)) (y := 1-2* jacobi.Reference.gamma a) (by norm_num)
  norm_num at hp2
  rw [h1] at hp2
  rw [h1,h2,← hp2,← Complex.ofReal_cpow Real.pi_pos.le]
  rw [Complex.Gamma_ofReal,Complex.Gamma_ofReal]
  push_cast
  rfl

/-- Every continued reference norm restricts exactly to the genuine original real norm integral at the same index.
Use: the analytic GL construction retains the actual source weights, rather than an independently normalized replacement family.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the continued normalization has the exact real value. The
original real norm integral has its already proved Gamma formula,
and real inclusion preserves every factor of that same quotient. -/
theorem norming_real {a : ℝ} (ha : -1<a) (k : ℕ) :
    norming (a:ℂ) k=(jacobi.Reference.norming a k:ℂ) := by
  -- Rewrite the proved original integral formula before matching its two actual Gamma arguments.
  rw [norming,normConstant_real,gamma_real,jacobi.Reference.norming_formula ha]
  have h1 : (k:ℂ)+1=(((k:ℝ)+1:ℝ):ℂ) := by push_cast; rfl
  have h2 : (k:ℂ)+2*(jacobi.Reference.gamma a:ℂ)=(((k:ℝ)+2* jacobi.Reference.gamma a:ℝ):ℂ) := by push_cast; rfl
  rw [h1,h2,Complex.Gamma_ofReal,Complex.Gamma_ofReal]
  push_cast
  rfl

end
end jacobi.ComplexReference
