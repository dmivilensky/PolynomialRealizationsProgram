import polyak.Boundary.P1.Spectrum
import polyak.Boundary.P5.RealChebyshev

/-!
Article: Appendix B, (p1slackpoly).
Use: scaled Chebyshev recurrences specify honest polynomial sources at z=0.
All inverse powers are removed before finite Bernstein annotations are consulted.
-/
noncomputable section
namespace polyak.Boundary.P1
open Spectral

def radialT {R : Type*} [CommRing R] : ℕ → R → R
  | 0,_ => 1
  | 1,_ => 1
  | n+2,z => 2*radialT (n+1) z-z^2*radialT n z

def radialU {R : Type*} [CommRing R] : ℕ → R → R
  | 0,_ => 1
  | 1,_ => 2
  | n+2,z => 2*radialU (n+1) z-z^2*radialU n z

theorem radialT_eq {z : ℝ} (hz : z≠0) (n : ℕ) : radialT n z=z^n*chebT n (1/z) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [radialT,chebT]
  | one => simp [radialT,chebT,hz]
  | more n ih ih1 =>
    rw [radialT,Spiral.chebT_recurrence,ih,ih1]
    simp only [pow_succ]
    field_simp [hz]

theorem radialU_eq {z : ℝ} (hz : z≠0) (n : ℕ) : radialU n z=z^n*chebU n (1/z) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [radialU,chebU]
  | one =>
    simp [radialU,chebU]
    field_simp
  | more n ih ih1 =>
    rw [radialU,P5.chebU_recurrence,ih,ih1]
    simp only [pow_succ]
    field_simp [hz]

def plainT {R : Type*} [CommRing R] : ℕ → R → R
  | 0,_ => 1
  | 1,a => a
  | n+2,a => 2*a*plainT (n+1) a-plainT n a

def plainU {R : Type*} [CommRing R] : ℕ → R → R
  | 0,_ => 1
  | 1,a => 2*a
  | n+2,a => 2*a*plainU (n+1) a-plainU n a

theorem plainT_eq (n : ℕ) (a : ℝ) : plainT n a=chebT n a := by
  induction n using Nat.twoStepInduction with
  | zero => simp [plainT,chebT]
  | one => simp [plainT,chebT]
  | more n ih ih1 => rw [plainT,Spiral.chebT_recurrence,ih,ih1]

theorem plainU_eq (n : ℕ) (a : ℝ) : plainU n a=chebU n a := by
  induction n using Nat.twoStepInduction with
  | zero => simp [plainU,chebU]
  | one => simp [plainU,chebU]
  | more n ih ih1 => rw [plainU,P5.chebU_recurrence,ih,ih1]

@[simp] theorem map_radialT {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (z : R) : f (radialT n z)=radialT n (f z) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [radialT]
  | one => simp [radialT]
  | more n ih ih1 => simp only [radialT,map_sub,map_mul,map_ofNat,map_pow,ih,ih1]

@[simp] theorem map_radialU {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (z : R) : f (radialU n z)=radialU n (f z) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [radialU]
  | one => simp only [radialU,map_ofNat]
  | more n ih ih1 => simp only [radialU,map_sub,map_mul,map_ofNat,map_pow,ih,ih1]

@[simp] theorem map_plainT {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (a : R) : f (plainT n a)=plainT n (f a) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [plainT]
  | one => rfl
  | more n ih ih1 => simp only [plainT,map_sub,map_mul,map_ofNat,ih,ih1]

@[simp] theorem map_plainU {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (a : R) : f (plainU n a)=plainU n (f a) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [plainU]
  | one => simp only [plainU,map_mul,map_ofNat]
  | more n ih ih1 => simp only [plainU,map_sub,map_mul,map_ofNat,ih,ih1]

def polynomialSlack {R : Type*} [CommRing R] (n : ℕ) (σ z a : R) : R :=
  (1+z*a)*radialT n z-z^n*(1+z*a)*plainT n a+
    σ*z^(n-1)*(2+z*a+z^2*(a^2-1))*plainU (n-1) a-
    σ*(1+z*a+z^2*(2*a^2-1))*radialU (n-1) z

@[simp] theorem map_polynomialSlack {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (σ z a : R) :
    f (polynomialSlack n σ z a)=polynomialSlack n (f σ) (f z) (f a) := by
  simp only [polynomialSlack,map_sub,map_mul,map_add,map_one,map_pow,map_ofNat,
    map_radialT,map_radialU,map_plainT,map_plainU]

def scaledSlack (n : ℕ) (σ z a : ℝ) : ℝ :=
  (1+z*a)*radialT n z-z^n*(1+z*a)*chebT n a+
    σ*z^(n-1)*contactD z a*chebU (n-1) a-σ*contactE z a*radialU (n-1) z

theorem polynomialSlack_eq (n : ℕ) (σ z a : ℝ) :
    polynomialSlack n σ z a=scaledSlack n σ z a := by
  simp only [polynomialSlack,scaledSlack,plainT_eq,plainU_eq,contactD,contactE]

theorem scaledSlack_source {z u a : ℝ} (hz : z≠0) (hD : contactD z a≠0)
    (h0 : quartic z u a=0) (n : ℕ) (hn : 1≤n) (σ : ℝ) :
    contactD z a*z^(n-1)*rawSlack u (1/z) (chargeNumerator z u a) n σ a=
      2*u*(1-a^2)*scaledSlack n σ z a := by
  have hact := contact_gap_identity h0
  have hd : chargeNumerator z u a*contactD z a=2*u*(1-a^2)*contactE z a := by
    unfold chargeNumerator
    field_simp [hD]
  have hs : contactD z a*rawSlack u (1/z) (chargeNumerator z u a) n σ a=
      2*u*(1-a^2)*(z*(1+z*a)*(chebT n (1/z)-chebT n a)+
        σ*contactD z a*chebU (n-1) a-σ*contactE z a*chebU (n-1) (1/z)) := by
    calc
      _=((1-a^2-u^2)*contactD z a)*(chebT n (1/z)-chebT n a)+
          σ*(2*u*(1-a^2)*contactD z a*chebU (n-1) a)-
          σ*(chargeNumerator z u a*contactD z a)*chebU (n-1) (1/z) := by
            unfold rawSlack lagDenominator
            ring
      _=_ := by rw [hact,hd]; ring
  have hp : z^n=z^(n-1)*z := by
    rw [← pow_succ,Nat.sub_add_cancel hn]
  calc
    _=z^(n-1)*(contactD z a*rawSlack u (1/z) (chargeNumerator z u a) n σ a) := by ring
    _=z^(n-1)*(2*u*(1-a^2)*(z*(1+z*a)*(chebT n (1/z)-chebT n a)+
        σ*contactD z a*chebU (n-1) a-σ*contactE z a*chebU (n-1) (1/z))) := by rw [hs]
    _=_ := by
      unfold scaledSlack
      rw [radialT_eq hz,radialU_eq hz,hp]
      ring

theorem rawSlack_nonneg_of_scaled {z u a : ℝ} (hz : 0<z) (hD : 0<contactD z a)
    (hu : 0≤u) (ha : a^2≤1) (h0 : quartic z u a=0) (n : ℕ) (hn : 1≤n)
    (σ : ℝ) (hscaled : 0≤scaledSlack n σ z a) :
    0≤rawSlack u (1/z) (chargeNumerator z u a) n σ a := by
  have he := scaledSlack_source hz.ne' hD.ne' h0 n hn σ
  have hprod : 0≤2*u*(1-a^2)*scaledSlack n σ z a := by positivity
  rw [← he] at hprod
  exact nonneg_of_mul_nonneg_right hprod (mul_pos hD (pow_pos hz _))

end polyak.Boundary.P1
