import polyak.FiniteHorizon.PriceCoefficients
import polyak.Waves.Mixture

/-!
Article: Appendix C, the actual stationary price in Lemma kernel.
Use: every continuous linear window price is one continuous spectral integral
plus one explicit scalar multiple of the common value parameter C, for every
probability spectrum, including non-atomic ones and infeasible pairs.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth.FiniteHorizon Spectral MeasureTheory Waves
open scoped BigOperators Matrix.Norms.Elementwise

/-- Actual Y_H of the arbitrary-mixture stationary table in its real L² Hilbert space. -/
def stationaryWindow (ν : Spectrum) (m : C(Frequency,ℂ)) (C t : ℝ) (H : ℕ) : WindowSpace H :=
  (Matrix.gram ℝ (fun i : Fin (H+2) => mixturePosition ν t (some i.val)),
    fun i : Fin H => mixtureValue ν m C t (some (i.val+1)))

def stationaryMatrixMap (t : ℝ) (i j : ℕ) : C(Frequency,ℝ) where
  toFun c:=inner ℝ (positionMap t (some i) c) (positionMap t (some j) c)
  continuous_toFun:=by fun_prop

def stationaryPriceIntegrand {H : ℕ} (L : WindowPrice H) (m : C(Frequency,ℂ)) (t : ℝ) :
    C(Frequency,ℝ) where
  toFun c:=(∑ i : Fin (H+2), ∑ j : Fin (H+2),
    L (matrixCoordinate i j)*stationaryMatrixMap t i.val j.val c)+
    ∑ i : Fin H,L (valueBasis i)*Real.exp (2*((i.val : ℝ)+1)*t)/2*(m c).re
  continuous_toFun:=by fun_prop

def stationaryPriceCharge {H : ℕ} (L : WindowPrice H) (t : ℝ) : ℝ :=
  ∑ i : Fin H,L (valueBasis i)*Real.exp (2*((i.val : ℝ)+1)*t)/4

theorem stationaryPriceIntegrand_integral {H : ℕ} (L : WindowPrice H) (m : C(Frequency,ℂ))
    (t : ℝ) (ν : Spectrum) :
    (∫ c,stationaryPriceIntegrand L m t c ∂ν)=
      (∑ i : Fin (H+2),∑ j : Fin (H+2),L (matrixCoordinate i j)*
        ∫ c,stationaryMatrixMap t i.val j.val c ∂ν)+
      ∑ i : Fin H,L (valueBasis i)*Real.exp (2*((i.val : ℝ)+1)*t)/2*
        avg ν (fun c => (m c).re) := by
  change (∫ c,(∑ i : Fin (H+2),∑ j : Fin (H+2),
      L (matrixCoordinate i j)*stationaryMatrixMap t i.val j.val c)+
      ∑ i : Fin H,L (valueBasis i)*Real.exp (2*((i.val : ℝ)+1)*t)/2*(m c).re ∂ν)=_
  rw [integral_add (integrable_continuous ν (by fun_prop)) (integrable_continuous ν (by fun_prop))]
  congr 1
  · rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum]
      · simp only [integral_const_mul]
      · intro j _
        exact integrable_continuous ν (by fun_prop)
    · intro i _
      exact integrable_continuous ν (by fun_prop)
  · rw [integral_finsetSum]
    · simp only [integral_const_mul,avg]
    · intro i _
      exact integrable_continuous ν (by fun_prop)

/-- The actual stationary window price is affine in C, with one continuous integrand.
No feasibility assumption is imposed on ν or C. -/
theorem price_stationaryWindow_eq {H : ℕ} (L : WindowPrice H) (m : C(Frequency,ℂ))
    (t : ℝ) (ν : Spectrum) (C : ℝ) :
    L (stationaryWindow ν m C t H)=
      (∫ c,stationaryPriceIntegrand L m t c ∂ν)+stationaryPriceCharge L t*C := by
  have he : L (stationaryWindow ν m C t H)=
      (∑ i : Fin (H+2),∑ j : Fin (H+2),
        (stationaryWindow ν m C t H).1 i j*L (matrixCoordinate i j))+
      ∑ i : Fin H,(stationaryWindow ν m C t H).2 i*L (valueBasis i) := by
    conv_lhs => rw [window_coordinate_expansion (stationaryWindow ν m C t H)]
    simp only [map_add,map_sum,map_smul,smul_eq_mul]
  rw [he,stationaryPriceIntegrand_integral]
  simp only [stationaryWindow,Matrix.gram_apply,mixturePosition,inner_lift,mixtureValue_some]
  unfold stationaryPriceCharge
  rw [Finset.sum_mul]
  have hm (i : Fin (H+2)) (j : Fin (H+2)) :
      (∫ c,inner ℝ (positionMap t (some i.val) c) (positionMap t (some j.val) c) ∂ν)*
        L (matrixCoordinate i j)=L (matrixCoordinate i j)*
        ∫ c,stationaryMatrixMap t i.val j.val c ∂ν := mul_comm _ _
  simp_rw [hm]
  rw [add_assoc]
  apply congrArg (fun z : ℝ =>
    (∑ i : Fin (H+2),∑ j : Fin (H+2),L (matrixCoordinate i j)*
      ∫ c,stationaryMatrixMap t i.val j.val c ∂ν)+z)
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

end polyak.FiniteHorizon
