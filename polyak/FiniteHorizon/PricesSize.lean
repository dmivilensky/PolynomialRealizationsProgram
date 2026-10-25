import polyak.FiniteHorizon.Prices

/-!
Article: Appendix C, the uniform coefficient bound in Lemma prices.
Use: explicit relative discount factors are bounded on every bounded exponent
interval; the bound is independent of the number of real squared filters.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth.FiniteHorizon
open scoped BigOperators Matrix.Norms.Elementwise

theorem priceSize_smul {H : ℕ} (r : ℝ) (L : WindowPrice H) :
    priceSize (r • L)=|r| *priceSize L := by
  simp [priceSize,smul_apply,smul_eq_mul,abs_mul,Finset.mul_sum,mul_add]

theorem priceSize_add_le {H : ℕ} (L K : WindowPrice H) :
    priceSize (L+K)≤priceSize L+priceSize K := by
  unfold priceSize
  simp only [add_apply]
  calc
    _≤(∑ i,∑ j,(|L (matrixCoordinate i j)|+|K (matrixCoordinate i j)|))+
        ∑ i,(|L (valueBasis i)|+|K (valueBasis i)|) := by
      apply add_le_add
      · exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => abs_add_le _ _
      · exact Finset.sum_le_sum fun i _ => abs_add_le _ _
    _=_ := by simp_rw [Finset.sum_add_distrib]; ring

theorem priceSize_sum_le {H : ℕ} {J : Type*} (S : Finset J) (L : J → WindowPrice H) :
    priceSize (∑ j ∈ S,L j)≤∑ j ∈ S,priceSize (L j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [priceSize]
  | @insert j S hj ih =>
    rw [Finset.sum_insert hj,Finset.sum_insert hj]
    exact (priceSize_add_le _ _).trans (add_le_add le_rfl ih)

theorem priceSize_matrixCoordinateNat_le (H a b : ℕ) : priceSize (matrixCoordinateNat H a b)≤1 := by
  classical
  unfold matrixCoordinateNat
  split_ifs
  · simp [priceSize,windowMatrixCoordinate_apply,matrixCoordinate,valueBasis,Matrix.single_apply,ite_and]
    simp only [apply_ite abs,abs_zero,abs_one]
    simp
  · simp [priceSize]
  · simp [priceSize]

theorem priceSize_valueCoordinateNat_le (H a : ℕ) : priceSize (valueCoordinateNat H a)≤1 := by
  classical
  unfold valueCoordinateNat
  split_ifs
  · simp [priceSize,valueCoordinate,matrixCoordinate,valueBasis,ContinuousLinearMap.comp_apply,Pi.single_apply]
    simp only [apply_ite abs,abs_zero,abs_one]
    simp
  · simp [priceSize]

theorem price_discount_coefficient_le (t : ℝ) {r e : ℕ} (hr : r+e≤6) :
    Real.exp ((2-2*(r : ℝ)-(e : ℝ))*t)≤Real.exp (12*|t|) := by
  have hsum : (r : ℝ)+(e : ℝ)≤6:=by exact_mod_cast hr
  have hx : |2-2*(r : ℝ)-(e : ℝ)|≤12:=by
    apply abs_le.mpr
    constructor <;> nlinarith [Nat.cast_nonneg (α:=ℝ) r,Nat.cast_nonneg (α:=ℝ) e]
  apply Real.exp_le_exp.mpr
  calc
    _≤|(2-2*(r : ℝ)-(e : ℝ))*t|:=le_abs_self _
    _=|2-2*(r : ℝ)-(e : ℝ)| *|t|:=abs_mul _ _
    _≤_:=mul_le_mul_of_nonneg_right hx (abs_nonneg _)

theorem rawWindowPrice7_size_le (H : ℕ) (t : ℝ) (μ : ℕ → ℕ → ℝ) (d : ℕ → ℝ) :
    priceSize (rawWindowPrice7 H t μ d)≤Real.exp (12*|t|)*rowPrimitiveSize 7 μ d := by
  let R:=Real.exp (12*|t|)
  have hquad (e : ℕ) (he : e∈Finset.range 8) :
      (∑ s ∈ Finset.range (8-e),priceSize (μ e s •
        ∑ r ∈ Finset.range s,Real.exp ((2-2*(r : ℝ)-(e : ℝ))*t) •
          matrixCoordinateNat H (H-6+r) (H-6+r+e)))≤R*primitiveSize (7-e) (μ e) := by
    unfold primitiveSize
    have he' : 7-e+1=8-e:=by have h:=Finset.mem_range.mp he; omega
    rw [he',Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    rw [priceSize_smul]
    calc
      _≤|μ e s| *(∑ r ∈ Finset.range s,priceSize
          (Real.exp ((2-2*(r : ℝ)-(e : ℝ))*t) •matrixCoordinateNat H (H-6+r) (H-6+r+e))) :=
        mul_le_mul_of_nonneg_left (priceSize_sum_le _ _) (abs_nonneg _)
      _≤|μ e s| *(∑ _r ∈ Finset.range s,R) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum
        intro r hr
        rw [priceSize_smul,abs_of_pos (Real.exp_pos _)]
        have hb : r+e≤6:=by have h:=Finset.mem_range.mp hs; have h':=Finset.mem_range.mp hr; omega
        exact (mul_le_of_le_one_right (Real.exp_pos _).le (priceSize_matrixCoordinateNat_le _ _ _)).trans
          (price_discount_coefficient_le t hb)
      _=_:=by simp; ring
  have hvalue (s : ℕ) (hs : s∈Finset.range 8) :
      priceSize (d s •∑ r ∈ Finset.range s,Real.exp ((2-2*(r : ℝ))*t) •
        valueCoordinateNat H (H-7+r))≤R*(|d s| *(s : ℝ)) := by
    rw [priceSize_smul]
    calc
      _≤|d s| *(∑ r ∈ Finset.range s,priceSize
          (Real.exp ((2-2*(r : ℝ))*t) •valueCoordinateNat H (H-7+r))) :=
        mul_le_mul_of_nonneg_left (priceSize_sum_le _ _) (abs_nonneg _)
      _≤|d s| *(∑ _r ∈ Finset.range s,R) :=by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply Finset.sum_le_sum
        intro r hr
        rw [priceSize_smul,abs_of_pos (Real.exp_pos _)]
        have hb : r+0≤6:=by have h:=Finset.mem_range.mp hs; have h':=Finset.mem_range.mp hr; omega
        have he:=price_discount_coefficient_le t hb
        norm_num only [Nat.cast_zero,sub_zero] at he
        exact (mul_le_of_le_one_right (Real.exp_pos _).le (priceSize_valueCoordinateNat_le _ _)).trans he
      _=_:=by simp; ring
  unfold rawWindowPrice7
  apply (priceSize_add_le _ _).trans
  calc
    _≤(∑ e ∈ Finset.range 8, ∑ s ∈ Finset.range (8-e),priceSize (μ e s •
        ∑ r ∈ Finset.range s,Real.exp ((2-2*(r : ℝ)-(e : ℝ))*t) •
          matrixCoordinateNat H (H-6+r) (H-6+r+e)))+
      ∑ s ∈ Finset.range 8,priceSize (d s •∑ r ∈ Finset.range s,
        Real.exp ((2-2*(r : ℝ))*t) •valueCoordinateNat H (H-7+r)) := by
      apply add_le_add
      · exact (priceSize_sum_le _ _).trans (Finset.sum_le_sum fun e _ => priceSize_sum_le _ _)
      · exact priceSize_sum_le _ _
    _≤(∑ e ∈ Finset.range 8,R*primitiveSize (7-e) (μ e))+
        ∑ s ∈ Finset.range 8,R*(|d s| *(s : ℝ)) :=
      add_le_add (Finset.sum_le_sum hquad) (Finset.sum_le_sum hvalue)
    _=_:=by unfold rowPrimitiveSize primitiveSize; simp_rw [←Finset.mul_sum]; ring

/-- Uniform actual price size, with the source telescoping constant and no filter-count dependence. -/
theorem windowPrice7_size_le {C : WindowMatrix7} {d : ℕ → ℝ} {ε : ℝ}
    (data : BandedData7 C d ε) (hε : 0≤ε) (H : ℕ) (a t : ℝ) :
    priceSize (windowPrice7 data H a t)≤|1/a| *Real.exp (12*|t|)*63*(bandedSize7 C d+ε) := by
  unfold windowPrice7
  rw [priceSize_smul,abs_neg]
  apply (mul_le_mul_of_nonneg_left (rawWindowPrice7_size_le _ _ _ _) (abs_nonneg _)).trans
  have hs:=banded_primitiveSize_le7 C d hε data.factors 1
  have hm:=mul_le_mul_of_nonneg_left hs
    (show 0≤|1/a| *Real.exp (12*|t|) by positivity)
  nlinarith

end polyak.FiniteHorizon
