import polyak.FiniteHorizon.StationaryWindow
import polyak.FiniteHorizon.Prices

/-!
Article: Appendix C, the actual linear price as a dense banded functional.
Use: its quadratic coefficients and value charge are explicit; stationary
evaluation has precisely the affine C coefficient used in kernel separation.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy Growth.FiniteHorizon Spectral Waves MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise

theorem price_apply_coordinates {H : ℕ} (L : WindowPrice H) (Y : WindowSpace H) :
    L Y=(∑ i,∑ j,L (matrixCoordinate i j)*Y.1 i j)+∑ i,L (valueBasis i)*Y.2 i := by
  have he:=congrArg (fun K : WindowPrice H => K Y) (priceOfCoefficients_inverse L)
  rw [priceOfCoefficients_apply] at he
  exact he.symm

def priceQuadraticCoefficients {H : ℕ} (L : WindowPrice H) (t : ℝ) :
    Fin (H+2) → Fin (H+2) → ℝ :=
  fun a b => Real.exp (((a.val : ℝ)+(b.val : ℝ))*t)*L (matrixCoordinate a b)

def priceValueCoefficients {H : ℕ} (L : WindowPrice H) (t : ℝ) (i : Fin H) : ℝ :=
  Real.exp (2*((i.val : ℝ)+1)*t)*L (valueBasis i)

def priceValueCharge {H : ℕ} (L : WindowPrice H) (t : ℝ) : ℝ :=
  ∑ i : Fin H, priceValueCoefficients L t i

def priceBandedEval {H : ℕ} (L : WindowPrice H) (t : ℝ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) : ℝ :=
  (∑ a : Fin (H+2),∑ b : Fin (H+2),priceQuadraticCoefficients L t a b*
    inner ℝ (f (j+(a : ℤ))) (f (j+(b : ℤ))))+
    ∑ i : Fin H,priceValueCoefficients L t i*h (j+(i : ℤ)+1)

theorem priceValueCharge_eq {H : ℕ} (L : WindowPrice H) (t : ℝ) :
    priceValueCharge L t=4*stationaryPriceCharge L t := by
  unfold priceValueCharge priceValueCoefficients stationaryPriceCharge
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact cosine kernel of the dense quadratic part on the spectral carrier. -/
def priceCosineSymbol {H : ℕ} (L : WindowPrice H) (t : ℝ) : C(Frequency,ℝ) where
  toFun c:=∑ a : Fin (H+2),∑ b : Fin (H+2),priceQuadraticCoefficients L t a b*
    Real.cos (((a.val : ℝ)-(b.val : ℝ))*Real.arccos c)
  continuous_toFun:=by fun_prop

theorem stationaryMatrixMap_eq (t : ℝ) (a b : ℕ) (c : Frequency) :
    stationaryMatrixMap t a b c=Real.exp (((a : ℝ)+(b : ℝ))*t)*
      Real.cos (((a : ℝ)-(b : ℝ))*Real.arccos c) := by
  change inner ℝ (z t (Real.arccos c)^a) (z t (Real.arccos c)^b)=_
  rw [Complex.inner]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,z_pow_re,z_pow_im]
  rw [sub_mul,Real.cos_sub,add_mul,Real.exp_add]
  ring

/-- The affine integrand of the actual price is exactly its banded quadratic
symbol plus half its value charge times Re m. -/
theorem stationaryPriceIntegrand_eq {H : ℕ} (L : WindowPrice H) (m : C(Frequency,ℂ))
    (t : ℝ) (c : Frequency) :
    stationaryPriceIntegrand L m t c=priceCosineSymbol L t c+
      (priceValueCharge L t/2)*(m c).re := by
  change (∑ i : Fin (H+2),∑ j : Fin (H+2),L (matrixCoordinate i j)*stationaryMatrixMap t i.val j.val c)+
    (∑ i : Fin H,L (valueBasis i)*Real.exp (2*((i.val : ℝ)+1)*t)/2*(m c).re)=_
  unfold priceCosineSymbol
  simp_rw [stationaryMatrixMap_eq]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    unfold priceQuadraticCoefficients
    ring
  · unfold priceValueCharge priceValueCoefficients
    rw [Finset.sum_div,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Exact stationary evaluation of the dense price functional, in the source
symbol/charge form, for arbitrary spectra and arbitrary common values. -/
theorem price_stationary_symbol_charge {H : ℕ} (L : WindowPrice H) (m : C(Frequency,ℂ))
    (t : ℝ) (ν : Spectrum) (C : ℝ) :
    L (stationaryWindow ν m C t H)=
      (∫ c,priceCosineSymbol L t c ∂ν)+
      (priceValueCharge L t/4)*(C+2*avg ν (fun c => (m c).re)) := by
  rw [price_stationaryWindow_eq]
  simp_rw [stationaryPriceIntegrand_eq]
  have hi : Integrable (fun c : Frequency => priceValueCharge L t/2*(m c).re)
      (ν : Measure Frequency):=integrable_continuous ν (by fun_prop)
  have hcharge : stationaryPriceCharge L t=priceValueCharge L t/4:=by
    have he:=priceValueCharge_eq L t
    linarith
  rw [integral_add (integrable_continuous ν (priceCosineSymbol L t).continuous) hi,
    integral_const_mul,hcharge]
  unfold avg
  ring

theorem priceQuadratic_discount {H : ℕ} (L : WindowPrice H) (t : ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ℤ → E) (j : ℤ) (a b : Fin (H+2)) :
    priceQuadraticCoefficients L t a b*
      inner ℝ (integerDiscount x t (j+(a : ℤ))) (integerDiscount x t (j+(b : ℤ)))=
      Real.exp (-2*(j : ℝ)*t)*
        (L (matrixCoordinate a b)*inner ℝ (x (j+(a : ℤ))) (x (j+(b : ℤ)))) := by
  unfold priceQuadraticCoefficients integerDiscount
  rw [real_inner_smul_left,real_inner_smul_right]
  have he : Real.exp (((a.val : ℝ)+(b.val : ℝ))*t)*
      Real.exp (-((j+(a : ℤ) : ℤ) : ℝ)*t)*Real.exp (-((j+(b : ℤ) : ℤ) : ℝ)*t)=
      Real.exp (-2*(j : ℝ)*t) := by
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    push_cast
    ring
  calc
    _=(Real.exp (((a.val : ℝ)+(b.val : ℝ))*t)*
        Real.exp (-((j+(a : ℤ) : ℤ) : ℝ)*t)*Real.exp (-((j+(b : ℤ) : ℤ) : ℝ)*t))*
        (L (matrixCoordinate a b)*inner ℝ (x (j+(a : ℤ))) (x (j+(b : ℤ)))) :=by ring
    _=_:=by rw [he]

theorem priceValue_discount {H : ℕ} (L : WindowPrice H) (t : ℝ)
    (v : ℤ → ℝ) (j : ℤ) (i : Fin H) :
    priceValueCoefficients L t i*integerDiscountValue v t (j+(i : ℤ)+1)=
      Real.exp (-2*(j : ℝ)*t)*(L (valueBasis i)*v (j+(i : ℤ)+1)) := by
  unfold priceValueCoefficients integerDiscountValue
  have he : Real.exp (2*((i.val : ℝ)+1)*t)*Real.exp (-2*((j+(i : ℤ)+1 : ℤ) : ℝ)*t)=
      Real.exp (-2*(j : ℝ)*t) := by
    rw [←Real.exp_add]
    congr 1
    push_cast
    ring
  calc
    _=(Real.exp (2*((i.val : ℝ)+1)*t)*Real.exp (-2*((j+(i : ℤ)+1 : ℤ) : ℝ)*t))*
        (L (valueBasis i)*v (j+(i : ℤ)+1)) :=by ring
    _=_:=by rw [he]

/-- Every continuous linear price is an actual finite-position/value banded
functional after discounting, with the explicit coefficients above. -/
theorem priceBandedEval_discounted {H : ℕ} (L : WindowPrice H) (t : ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : ℤ → E) (v : ℤ → ℝ) (j : ℤ) :
    priceBandedEval L t (integerDiscount x t) (integerDiscountValue v t) j=
      Real.exp (-2*(j : ℝ)*t)*L (integerWindow H x v (j+(H : ℤ))) := by
  rw [price_apply_coordinates]
  unfold priceBandedEval integerWindow
  have hi (i : Fin (H+2)) : j+(H : ℤ)-(H : ℤ)+(i : ℤ)=j+(i : ℤ):=by ring
  have hv (i : Fin H) : j+(H : ℤ)-(H : ℤ)+(i : ℤ)+1=j+(i : ℤ)+1:=by ring
  simp only [hi,hv]
  rw [mul_add,Finset.mul_sum,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    exact priceQuadratic_discount L t x j a b
  · apply Finset.sum_congr rfl
    intro i _
    exact priceValue_discount L t v j i

/-- Comparing the true stationary values for all common C forces zero charge
and identifies the exact source symbol, pointwise by Dirac spectra. -/
theorem zero_charge_and_symbol_of_stationary_identity (symbol target : C(Frequency,ℝ))
    (m : C(Frequency,ℂ)) (charge : ℝ)
    (he : ∀ (ν : Spectrum) (C : ℝ),
      (∫ c,symbol c ∂ν)+(charge/4)*(C+2*avg ν (fun c => (m c).re))=∫ c,target c ∂ν) :
    charge=0 ∧ symbol=target := by
  let c₀ : Frequency:=⟨0,by norm_num⟩
  let ν₀ : Spectrum:=⟨Measure.dirac c₀,by infer_instance⟩
  have h0:=he ν₀ 0
  have h4:=he ν₀ 4
  have hcharge : charge=0:=by linarith
  refine ⟨hcharge,?_⟩
  apply ContinuousMap.ext
  intro c
  let ν : Spectrum:=⟨Measure.dirac c,by infer_instance⟩
  have h:=he ν 0
  simp only [hcharge,zero_div,zero_mul,add_zero] at h
  change (∫ z,symbol z ∂Measure.dirac c)=∫ z,target z ∂Measure.dirac c at h
  simpa only [MeasureTheory.integral_dirac] using h

end polyak.FiniteHorizon
