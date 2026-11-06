import nesterov.Attainment.ComplexSymbols
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Finite lag dual symbols are Laurent polynomials. Multiplying by a fixed
unit-circle monomial gives an ordinary real polynomial with an explicit
degree bound. This avoids cancellations or division by the query polynomial. -/
noncomputable section
open Polynomial
namespace nesterov.Attainment

def ceval (q : Polynomial ℝ) (z : ℂ) : ℂ := (q.map Complex.ofRealHom).eval z

@[simp] theorem ceval_add (q r : Polynomial ℝ) (z : ℂ) : ceval (q+r) z=ceval q z+ceval r z := by simp [ceval]
@[simp] theorem ceval_sub (q r : Polynomial ℝ) (z : ℂ) : ceval (q-r) z=ceval q z-ceval r z := by simp [ceval]
@[simp] theorem ceval_mul (q r : Polynomial ℝ) (z : ℂ) : ceval (q*r) z=ceval q z*ceval r z := by simp [ceval]
@[simp] theorem ceval_C (r : ℝ) (z : ℂ) : ceval (C r) z=(r:ℂ) := by simp [ceval]
@[simp] theorem ceval_X (z : ℂ) : ceval X z=z := by simp [ceval]
@[simp] theorem ceval_pow (q : Polynomial ℝ) (n : ℕ) (z : ℂ) : ceval (q^n) z=(ceval q z)^n := by simp [ceval]

def radialPolynomial (q : Polynomial ℝ) (t : ℝ) : Polynomial ℝ :=
  q.comp (C (Real.exp t)*X)

def reflectedGap (D : ℕ) (u p : Polynomial ℝ) : Polynomial ℝ :=
  u*u.reflect D-p*p.reflect D

def reflectedCross (D : ℕ) (u p : Polynomial ℝ) : Polynomial ℝ :=
  p*u.reflect D-u*p.reflect D

def lagPolynomial (D M : ℕ) (u p : Polynomial ℝ) (s : ℝ) (n : ℕ) (δ : ℝ) : Polynomial ℝ :=
  reflectedGap D u p * (C (Real.cosh (n*s))*X^M-C (1/2)*(X^(M+n)+X^(M-n)))+
    C (δ/2)*reflectedCross D u p*(X^(M+n)-X^(M-n))

theorem radialPolynomial_natDegree_le (q : Polynomial ℝ) (t : ℝ) :
    (radialPolynomial q t).natDegree ≤ q.natDegree := by
  apply natDegree_comp_le.trans
  have h : (C (Real.exp t)*X : Polynomial ℝ).natDegree ≤ 1 := by
    simpa only [pow_one] using (natDegree_C_mul_X_pow_le (Real.exp t) 1)
  exact (Nat.mul_le_mul_left _ h).trans_eq (Nat.mul_one _)

theorem reflected_natDegree_le {D : ℕ} {u p : Polynomial ℝ}
    (hu : u.natDegree ≤ D) (hp : p.natDegree ≤ D) :
    (reflectedGap D u p).natDegree ≤ 2*D ∧ (reflectedCross D u p).natDegree ≤ 2*D := by
  have hu' : (u.reflect D).natDegree ≤ D := natDegree_reflect_le.trans (max_le le_rfl hu)
  have hp' : (p.reflect D).natDegree ≤ D := natDegree_reflect_le.trans (max_le le_rfl hp)
  have hmul (a b : Polynomial ℝ) (ha : a.natDegree ≤ D) (hb : b.natDegree ≤ D) :
      (a*b).natDegree ≤ 2*D := by
    exact natDegree_mul_le.trans (by omega)
  constructor
  · exact (natDegree_sub_le _ _).trans (max_le (hmul _ _ hu hu') (hmul _ _ hp hp'))
  · exact (natDegree_sub_le _ _).trans (max_le (hmul _ _ hp hu') (hmul _ _ hu hp'))

theorem lagPolynomial_natDegree_le {D M n : ℕ} {u p : Polynomial ℝ}
    (hu : u.natDegree ≤ D) (hp : p.natDegree ≤ D) (hn : n ≤ M) (s δ : ℝ) :
    (lagPolynomial D M u p s n δ).natDegree ≤ 2*(D+M) := by
  have hG := (reflected_natDegree_le hu hp).1
  have hH := (reflected_natDegree_le hu hp).2
  have hsum : (X^(M+n)+X^(M-n) : Polynomial ℝ).natDegree ≤ 2*M := by
    apply (natDegree_add_le _ _).trans
    simp only [natDegree_X_pow]
    exact max_le (by omega) (by omega)
  have hdiff : (X^(M+n)-X^(M-n) : Polynomial ℝ).natDegree ≤ 2*M := by
    apply (natDegree_sub_le _ _).trans
    simp only [natDegree_X_pow]
    exact max_le (by omega) (by omega)
  have hmid : (C (Real.cosh (n*s))*X^M-C (1/2)*(X^(M+n)+X^(M-n)) : Polynomial ℝ).natDegree ≤ 2*M := by
    apply (natDegree_sub_le _ _).trans
    exact max_le ((natDegree_C_mul_X_pow_le _ _).trans (by omega)) ((natDegree_C_mul_le _ _).trans hsum)
  apply (natDegree_add_le _ _).trans
  apply max_le
  · exact natDegree_mul_le.trans (by omega)
  · exact natDegree_mul_le.trans (by have := natDegree_C_mul_le (a := δ/2) (f := reflectedCross D u p); omega)

theorem ceval_conj (q : Polynomial ℝ) (z : ℂ) : ceval q (star z)=star (ceval q z) := by
  have hhom : Complex.ofRealHom=algebraMap ℝ ℂ := by ext r; rfl
  simpa only [ceval,Polynomial.aeval_def,Polynomial.eval_map,Complex.star_def,hhom] using
    Polynomial.aeval_conj q z (K := ℂ)

/-- Padded reflection is exactly conjugation on the unit circle. -/
theorem ceval_reflect_unit {D : ℕ} (q : Polynomial ℝ) (hq : q.natDegree ≤ D)
    (z : ℂ) (hz : ‖z‖=1) : ceval (q.reflect D) z = z^D*star (ceval q z) := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  let : Invertible (z⁻¹) := invertibleOfNonzero (inv_ne_zero hz0)
  have hh := Polynomial.eval₂_reflect_mul_pow Complex.ofRealHom (z⁻¹) D q hq
  simp only [invOf_eq_inv,inv_inv] at hh
  rw [← Polynomial.eval_map, ← Polynomial.eval_map] at hh
  change ceval (q.reflect D) z * (z⁻¹)^D=ceval q (z⁻¹) at hh
  rw [Complex.inv_eq_conj hz,← Complex.star_def,ceval_conj] at hh
  have hpow : (star z)^D*z^D=1 := by
    rw [← mul_pow,Complex.star_def,← Complex.inv_eq_conj hz,inv_mul_cancel₀ hz0,one_pow]
  calc
    _ = (ceval (q.reflect D) z*(star z)^D)*z^D := by rw [mul_assoc,hpow,mul_one]
    _ = star (ceval q z)*z^D := by rw [hh]
    _ = _ := mul_comm _ _

theorem ceval_reflectedGap {D : ℕ} (u p : Polynomial ℝ) (hu : u.natDegree ≤ D) (hp : p.natDegree ≤ D)
    (z : ℂ) (hz : ‖z‖=1) :
    ceval (reflectedGap D u p) z = z^D*
      ((Complex.normSq (ceval u z)-Complex.normSq (ceval p z) : ℝ) : ℂ) := by
  rw [reflectedGap,ceval_sub,ceval_mul,ceval_mul]
  rw [ceval_reflect_unit u hu z hz,ceval_reflect_unit p hp z hz,← gap_complex_identity]
  ring

theorem ceval_reflectedCross {D : ℕ} (u p : Polynomial ℝ) (hu : u.natDegree ≤ D) (hp : p.natDegree ≤ D)
    (z : ℂ) (hz : ‖z‖=1) :
    ceval (reflectedCross D u p) z = z^D*(2*Complex.I)*((ceval p z*star (ceval u z)).im : ℂ) := by
  rw [reflectedCross,ceval_sub,ceval_mul,ceval_mul]
  rw [ceval_reflect_unit u hu z hz,ceval_reflect_unit p hp z hz]
  have he := (div_eq_iff (by norm_num : (2*Complex.I : ℂ) ≠ 0)).mp
    (skew_complex_identity (ceval u z) (ceval p z))
  linear_combination z^D*he

theorem norm_unitPhase (ω : ℝ) : ‖polyak.Waves.z 0 ω‖=1 := by
  simpa only [pow_one,mul_zero,Real.exp_zero] using polyak.Waves.norm_z_pow 0 ω 1

theorem unitPhase_sums (ω : ℝ) (n : ℕ) :
    polyak.Waves.z 0 ω^n+(polyak.Waves.z 0 ω)⁻¹^n=(2 : ℂ)*(Real.cos (n*ω) : ℂ) ∧
    polyak.Waves.z 0 ω^n-(polyak.Waves.z 0 ω)⁻¹^n=(2*Complex.I : ℂ)*(Real.sin (n*ω) : ℂ) := by
  rw [Complex.inv_eq_conj (norm_unitPhase ω),← map_pow]
  constructor <;> apply Complex.ext <;>
    simp only [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
      Complex.conj_re,Complex.conj_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      polyak.Waves.z_pow_re,polyak.Waves.z_pow_im,mul_zero,Real.exp_zero,one_mul]
  all_goals norm_num
  all_goals ring

def signedLagValue (u p : ℂ) (s ω : ℝ) (n : ℕ) (δ : ℝ) : ℝ :=
  (Complex.normSq u-Complex.normSq p)*(Real.cosh (n*s)-Real.cos (n*ω))-
    δ*(2*(p*star u).im*Real.sin (n*ω))

/-- The finite ordinary real polynomial exactly represents the signed lag
on the unit circle, after multiplying by the common monomial. -/
theorem ceval_lagPolynomial_unit {D M n : ℕ} (u p : Polynomial ℝ)
    (hu : u.natDegree ≤ D) (hp : p.natDegree ≤ D) (hn : n ≤ M) (s δ ω : ℝ) :
    ceval (lagPolynomial D M u p s n δ) (polyak.Waves.z 0 ω) =
      polyak.Waves.z 0 ω^(D+M) *
        (signedLagValue (ceval u (polyak.Waves.z 0 ω)) (ceval p (polyak.Waves.z 0 ω)) s ω n δ : ℂ) := by
  let z := polyak.Waves.z 0 ω
  have hz : z ≠ 0 := polyak.Waves.z_ne_zero 0 ω
  have hplus : z^(M+n)+z^(M-n)=z^M*((2 : ℂ)*(Real.cos (n*ω) : ℂ)) := by
    rw [pow_add,pow_sub₀ z hz hn,← inv_pow,← mul_add]
    exact congrArg (fun w : ℂ => z^M*w) (unitPhase_sums ω n).1
  have hminus : z^(M+n)-z^(M-n)=z^M*((2*Complex.I : ℂ)*(Real.sin (n*ω) : ℂ)) := by
    rw [pow_add,pow_sub₀ z hz hn,← inv_pow,← mul_sub]
    exact congrArg (fun w : ℂ => z^M*w) (unitPhase_sums ω n).2
  simp only [lagPolynomial,ceval_add,ceval_mul,ceval_sub,ceval_C,ceval_pow,ceval_X]
  rw [ceval_reflectedGap u p hu hp _ (norm_unitPhase ω),
    ceval_reflectedCross u p hu hp _ (norm_unitPhase ω),hplus,hminus,pow_add]
  unfold signedLagValue
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem ceval_radialPolynomial_phase (q : Polynomial ℝ) (t ω : ℝ) :
    ceval (radialPolynomial q t) (polyak.Waves.z 0 ω)=amplitude q t (ω : ℂ) := by
  simp only [ceval,radialPolynomial,Polynomial.map_comp,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_X,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  congr 1
  change (Real.exp t : ℂ)*polyak.Waves.z 0 ω=Complex.exp ((t : ℂ)+(ω : ℂ)*Complex.I)
  unfold polyak.Waves.z
  rw [Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  simp

end nesterov.Attainment
