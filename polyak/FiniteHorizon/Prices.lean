import polyak.FiniteHorizon.BandedBranch
import polyak.FiniteHorizon.PriceCoefficients
import polyak.FiniteHorizon.PricesSeries

/-!
Article: Appendix C, the explicit finite-window prices of Lemma prices.
Use: the actual telescoping row primitive is a true continuous linear functional
of the Gram-and-value window; all relative discount coefficients are explicit.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy Growth Growth.FiniteHorizon
open scoped BigOperators Topology Matrix.Norms.Elementwise

def matrixCoordinateNat (H a b : ℕ) : WindowPrice H :=
  if ha : a<H+2 then if hb : b<H+2 then windowMatrixCoordinate ⟨a,ha⟩ ⟨b,hb⟩ else 0 else 0

def valueCoordinateNat (H a : ℕ) : WindowPrice H :=
  if ha : a<H then valueCoordinate ⟨a,ha⟩ else 0

/-- The undiscounted finite Gram window, with an integer center and all integer samples. -/
def integerWindow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : ℕ) (x : ℤ → E) (v : ℤ → ℝ) (k : ℤ) : WindowSpace H :=
  ((fun i j => inner ℝ (x (k-(H : ℤ)+(i : ℤ))) (x (k-(H : ℤ)+(j : ℤ)))),
    fun i => v (k-(H : ℤ)+(i : ℤ)+1))

def integerDiscount {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℤ → E) (t : ℝ) (i : ℤ) : E :=
  Real.exp (-(i : ℝ)*t) • x i

def integerDiscountValue (v : ℤ → ℝ) (t : ℝ) (i : ℤ) : ℝ :=
  Real.exp (-2*(i : ℝ)*t)*v i

/-- Exact price coefficients before the final factor −1/a. -/
def rawWindowPrice7 (H : ℕ) (t : ℝ) (μ : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : WindowPrice H :=
  (∑ e ∈ Finset.range 8, ∑ s ∈ Finset.range (8-e), μ e s •
    ∑ r ∈ Finset.range s, Real.exp ((2-2*(r : ℝ)-(e : ℝ))*t) •
      matrixCoordinateNat H (H-6+r) (H-6+r+e))+
  ∑ s ∈ Finset.range 8, d s •∑ r ∈ Finset.range s,
    Real.exp ((2-2*(r : ℝ))*t) • valueCoordinateNat H (H-7+r)

theorem rawWindowPrice7_apply (H : ℕ) (t : ℝ) (μ : ℕ → ℕ → ℝ) (d : ℕ → ℝ)
    (Y : WindowSpace H) : rawWindowPrice7 H t μ d Y=
    (∑ e ∈ Finset.range 8, ∑ s ∈ Finset.range (8-e), μ e s *
      ∑ r ∈ Finset.range s, Real.exp ((2-2*(r : ℝ)-(e : ℝ))*t)*
        matrixCoordinateNat H (H-6+r) (H-6+r+e) Y)+
      ∑ s ∈ Finset.range 8, d s *∑ r ∈ Finset.range s,
        Real.exp ((2-2*(r : ℝ))*t)*valueCoordinateNat H (H-7+r) Y := by
  simp [rawWindowPrice7]

theorem matrixCoordinateNat_integerWindow {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {H e r : ℕ} (hH : 7≤H) (hr : r+e≤6)
    (x : ℤ → E) (v : ℤ → ℝ) (k : ℤ) :
    matrixCoordinateNat H (H-6+r) (H-6+r+e) (integerWindow H x v k)=
      inner ℝ (x (k-6+r)) (x (k-6+r+e)) := by
  have h0 : H-6+r<H+2:=by omega
  have h1 : H-6+r+e<H+2:=by omega
  simp only [matrixCoordinateNat,dite_eq_left h0,dite_eq_left h1,windowMatrixCoordinate_apply,
    integerWindow]
  have hi : ((H-6 : ℕ) : ℤ)=(H : ℤ)-6:=by omega
  push_cast
  rw [hi]
  congr 2 <;> ring

theorem valueCoordinateNat_integerWindow {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {H r : ℕ} (hH : 7≤H) (hr : r≤6)
    (x : ℤ → E) (v : ℤ → ℝ) (k : ℤ) :
    valueCoordinateNat H (H-7+r) (integerWindow H x v k)=v (k-6+r) := by
  have h0 : H-7+r<H:=by omega
  simp only [valueCoordinateNat,dite_eq_left h0]
  change v (k-(H : ℤ)+((H-7+r : ℕ) : ℤ)+1)=_
  have hi : ((H-7 : ℕ) : ℤ)=(H : ℤ)-7:=by omega
  push_cast
  rw [hi]
  congr 1
  ring

theorem discounted_diagonal_scaling {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ℤ → E) (t : ℝ) (k : ℤ) (r e : ℕ) :
    Real.exp (2*((k : ℝ)-5)*t)*diagonalValue (integerDiscount x t) e (k-6+r)=
      Real.exp ((2-2*(r : ℝ)-(e : ℝ))*t)*inner ℝ (x (k-6+r)) (x (k-6+r+e)) := by
  simp only [diagonalValue,integerDiscount,real_inner_smul_left,real_inner_smul_right]
  rw [←mul_assoc,←mul_assoc,←Real.exp_add,←Real.exp_add]
  congr 2
  push_cast
  ring

theorem discounted_value_scaling (v : ℤ → ℝ) (t : ℝ) (k : ℤ) (r : ℕ) :
    Real.exp (2*((k : ℝ)-5)*t)*integerDiscountValue v t (k-6+r)=
      Real.exp ((2-2*(r : ℝ))*t)*v (k-6+r) := by
  unfold integerDiscountValue
  rw [←mul_assoc,←Real.exp_add]
  congr 2
  push_cast
  ring

/-- Exact identification with the genuine row primitive; all coefficients are independent of k. -/
theorem rawWindowPrice7_integerWindow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : ℕ} (hH : 7≤H) (t : ℝ) (μ : ℕ → ℕ → ℝ) (d : ℕ → ℝ)
    (x : ℤ → E) (v : ℤ → ℝ) (k : ℤ) :
    rawWindowPrice7 H t μ d (integerWindow H x v k)=
      Real.exp (2*((k : ℝ)-5)*t)*
        rowPrimitive 7 μ d (integerDiscount x t) (integerDiscountValue v t) (k-6) := by
  rw [rawWindowPrice7_apply]
  unfold rowPrimitive primitive prefixSum
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have he' : e<8:=Finset.mem_range.mp he
    have heq : 7-e+1=8-e:=by omega
    rw [heq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [mul_left_comm (Real.exp (2*((k : ℝ)-5)*t)) (μ e s)]
    apply congrArg (fun z : ℝ => μ e s*z)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hbound : r+e≤6:=by have hs':=Finset.mem_range.mp hs; have hr':=Finset.mem_range.mp hr; omega
    rw [matrixCoordinateNat_integerWindow hH hbound]
    exact (discounted_diagonal_scaling x t k r e).symm
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [mul_left_comm (Real.exp (2*((k : ℝ)-5)*t)) (d s)]
    apply congrArg (fun z : ℝ => d s*z)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r≤6:=by have hs':=Finset.mem_range.mp hs; have hr':=Finset.mem_range.mp hr; omega
    rw [valueCoordinateNat_integerWindow hH hr']
    exact (discounted_value_scaling v t k r).symm

/-- The actual price used above the rate, with M₀=5 and source gap ε=aδ. -/
def windowPrice7 {C : WindowMatrix7} {d : ℕ → ℝ} {ε : ℝ}
    (data : BandedData7 C d ε) (H : ℕ) (a t : ℝ) : WindowPrice H :=
  (-(1/a)) • rawWindowPrice7 H t (matrixRows7 (completedMatrix7 C data.factors 1)) d

theorem windowPrice7_integerWindow {C : WindowMatrix7} {d : ℕ → ℝ} {ε : ℝ}
    (data : BandedData7 C d ε) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : ℕ} (hH : 7≤H) (a t : ℝ) (x : ℤ → E) (v : ℤ → ℝ) (k : ℤ) :
    windowPrice7 data H a t (integerWindow H x v k)=
      -(1/a)*Real.exp (2*((k : ℝ)-5)*t)*
        data.primitive (integerDiscount x t) (integerDiscountValue v t) (k-5) := by
  simp only [windowPrice7,smul_apply,smul_eq_mul,rawWindowPrice7_integerWindow hH,
    BandedData7.primitive,bandedPrimitive7]
  rw [show k-5+(-1 : ℤ)=k-6 by ring]
  ring

theorem discounted_norm_scaling {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℤ → E) (t : ℝ) (j : ℤ) :
    Real.exp (2*(j : ℝ)*t)*‖integerDiscount x t j‖^2=‖x j‖^2 := by
  simp only [integerDiscount,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_pow]
  rw [←Real.exp_nat_mul,←mul_assoc,←Real.exp_add]
  norm_num only [Nat.cast_ofNat]
  have he : 2*(j : ℝ)*t+2*(-(j : ℝ)*t)=0:=by ring
  rw [he,Real.exp_zero,one_mul]

/-- The source telescoping identity proves the genuine price inequality on the
actual consecutive windows, without assuming a Lyapunov functional. -/
theorem windowPrice7_step {C : WindowMatrix7} {d : ℕ → ℝ} {ε a δ t : ℝ}
    (data : BandedData7 C d ε) (ha : 0<a) (hε : ε=a*δ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : ℕ} (hH : 7≤H) (x : ℤ → E) (v : ℤ → ℝ) (k : ℤ)
    (hB : 0≤bandedFunctional7 C d (integerDiscount x t) (integerDiscountValue v t) (k-6)) :
    δ*‖x (k-5)‖^2≤windowPrice7 data H a t (integerWindow H x v k)-
      Real.exp (-2*t)*windowPrice7 data H a t (integerWindow H x v (k+1)) := by
  have hs:=data.step (integerDiscount x t) (integerDiscountValue v t) (k-5)
    (by simpa only [show k-5-1=k-6 by ring] using hB)
  rw [windowPrice7_integerWindow data hH,windowPrice7_integerWindow data hH]
  have hexp : Real.exp (-2*t)*Real.exp (2*(((k+1 : ℤ) : ℝ)-5)*t)=
      Real.exp (2*((k : ℝ)-5)*t) := by
    rw [←Real.exp_add]
    congr 1
    push_cast
    ring
  have hn:=discounted_norm_scaling x t (k-5)
  have hmul:=mul_le_mul_of_nonneg_left hs
    (show 0≤(1/a)*Real.exp (2*((k : ℝ)-5)*t) by positivity)
  conv_lhs at hmul => rw [hε]
  have hleft : (1/a)*Real.exp (2*((k : ℝ)-5)*t)*(a*δ*‖integerDiscount x t (k-5)‖^2)=
      δ*‖x (k-5)‖^2 := by
    have hn' : Real.exp (2*((k : ℝ)-5)*t)*‖integerDiscount x t (k-5)‖^2=‖x (k-5)‖^2 := by
      simpa only [Int.cast_sub,Int.cast_ofNat] using hn
    calc
      _=δ*(Real.exp (2*((k : ℝ)-5)*t)*‖integerDiscount x t (k-5)‖^2) :=by field_simp [ha.ne']
      _=_:=by rw [hn']
  rw [hleft] at hmul
  have hshift : k+1-5=k-5+1:=by ring
  rw [hshift]
  calc
    _≤_:=hmul
    _=_:=by
      rw [show Real.exp (-2*t)*(-(1/a)*Real.exp (2*(((k+1 : ℤ) : ℝ)-5)*t)*
          data.primitive (integerDiscount x t) (integerDiscountValue v t) (k-5+1))=
          -(1/a)*(Real.exp (-2*t)*Real.exp (2*(((k+1 : ℤ) : ℝ)-5)*t))*
          data.primitive (integerDiscount x t) (integerDiscountValue v t) (k-5+1) by ring,
        hexp]
      ring

end polyak.FiniteHorizon
