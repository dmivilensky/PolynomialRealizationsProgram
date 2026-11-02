import krylov.Functions.HarmonicRealization
import krylov.Correction.ConstantBounds

/-!
Article: main_krylov, thm:H, comparison with the genuine sharp budget constant.
Use: prove an explicit relative O(r) estimate for the printed harmonic
coefficient against K(W,omega'), using the actual harmonic budgets.
Source: the proved scalar variational bounds and exact harmonic norm ratio.
-/

namespace krylov.Functions
noncomputable section
open krylov.Correction krylov.Reference krylov.Tensor krylov.Nonlinear Matrix Finset
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

/-- The harmonic one-half coefficient agrees with the genuine sharp budget
constant to relative error at most 9r on the entire small-r interval.
Article: main_krylov, thm:H, K(W,omega')(1+O(r)). -/
theorem harmonic_sharp_comparison (κ r : ℝ) (hκ : 0≤κ) (hr : 0≤r) (hr1 : r≤1) :
    |κ^2/2*harmonicResponseRatio r-sharpConstant (κ*(1+r)) (κ*r)| ≤
      9*r*sharpConstant (κ*(1+r)) (κ*r) := by
  let K := sharpConstant (κ*(1+r)) (κ*r)
  have hW : 0≤κ*(1+r) := by positivity
  have hw : 0≤κ*r := mul_nonneg hκ hr
  have hLo := sharpConstant_lower_quadratic hW hw
  have hHi := sharpConstant_upper hW hw
  have hWκ : κ≤κ*(1+r) := by nlinarith
  have hWsq := pow_le_pow_left₀ hκ hWκ 2
  have hKlo : κ^2/2≤K := by dsimp only [K]; linarith
  have hrsq : r^2≤r := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hrsq (sq_nonneg κ)
  have hKhi : K-κ^2/2≤(7/2 : ℝ)*κ^2*r := by dsimp only [K]; nlinarith only [hHi,hscaled]
  have hKabs : |κ^2/2-K|≤(7/2 : ℝ)*κ^2*r := by
    rw [abs_of_nonpos (by linarith : κ^2/2-K≤0)]
    linarith
  have hprod := mul_le_mul_of_nonneg_left (harmonicResponseRatio_error hr hr1)
    (by positivity : 0≤κ^2/2)
  have hp : |κ^2/2*harmonicResponseRatio r-κ^2/2|≤κ^2*r := by
    rw [show κ^2/2*harmonicResponseRatio r-κ^2/2=(κ^2/2)*(harmonicResponseRatio r-1) by ring,
      abs_mul,abs_of_nonneg (by positivity : 0≤κ^2/2)]
    nlinarith only [hprod]
  calc
    _ = |(κ^2/2*harmonicResponseRatio r-κ^2/2)+(κ^2/2-K)| := by
      dsimp only [K]
      congr 1
      ring
    _ ≤ |κ^2/2*harmonicResponseRatio r-κ^2/2|+|κ^2/2-K| := abs_add_le _ _
    _ ≤ κ^2*r+(7/2 : ℝ)*κ^2*r := add_le_add hp hKabs
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hKlo (by positivity : 0≤9*r)
      nlinarith only [hm]

/-- The original actual native cubic increments have exactly the printed
total harmonic budget, through the genuine physical third derivative.
Article: main_krylov, thm:H, W=a(sqrt(c_0)+sqrt(c_last)). -/
theorem native_harmonic_total_budget {n : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : EuclideanSpace ℝ (Fin n)) (hN : 3≤referenceAtomCount base hb (cgOperator base u))
    (a : ℝ) (ha : 0≤a) :
    (∑ l : Fin (referenceAtomCount base hb (cgOperator base u)-1),
      ‖rfcCompatibleIncrements base hb (metricCubicVariation (metricCoordinates base hb)
        (referenceHarmonicTensor base hb (cgOperator base u) a)) u l.val‖) =
      a*(‖canonicalCGStep base (cgOperator base u) 0‖+
        ‖canonicalCGStep base (cgOperator base u) (referenceAtomCount base hb (cgOperator base u)-1)‖) := by
  simp_rw [rfcCompatibleIncrements_metricCubic,cubicSliceMatrix_norm]
  exact reference_harmonic_total_budget base hb (cgOperator base u) hN a ha

/-- The original actual native final cubic correction has exactly the printed
harmonic correction budget. Article: main_krylov, thm:H, omega'=a sqrt(c_last). -/
theorem native_harmonic_correction_budget {n : ℕ}
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount base hb (cgOperator base u))
    (a : ℝ) (ha : 0≤a) :
    ‖rfcCompatibleCorrection base hb (metricCubicVariation (metricCoordinates base hb)
      (referenceHarmonicTensor base hb (cgOperator base u) a)) u
        (referenceAtomCount base hb (cgOperator base u)-1)‖ =
      a*‖canonicalCGStep base (cgOperator base u) (referenceAtomCount base hb (cgOperator base u)-1)‖ := by
  rw [rfcCompatibleCorrection_metricCubic,cubicSliceMatrix_norm]
  exact reference_harmonic_correction_norm base hb (cgOperator base u) hN a ha

end
end krylov.Functions
