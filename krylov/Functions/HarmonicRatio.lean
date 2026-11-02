import krylov.Functions.HarmonicNativeCoefficient

/-!
Article: main_krylov, thm:H, exact one-half coefficient and its ratio limit.
Use: retain the exact harmonic function response at every nonnegative
last/first step ratio and prove an explicit form of its printed 1+O(r).
Source: the genuine endpoint product and elementary square-root algebra.
-/

namespace krylov.Functions
noncomputable section
open Matrix krylov.Reference krylov.Correction krylov.Tensor
open scoped Matrix.Norms.L2Operator

/-- The exact dimensionless multiplier of the harmonic one-half coefficient.
Article: main_krylov, thm:H. -/
def harmonicResponseRatio (r : ℝ) : ℝ := |1-r| * Real.sqrt ((1+2*r)^2+r^2)

/-- The printed harmonic relative remainder is bounded explicitly by 2r on
the entire small-r interval. Article: main_krylov, thm:H, 1+O(r). -/
theorem harmonicResponseRatio_error {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |harmonicResponseRatio r-1| ≤ 2*r := by
  have hs0 : 0 ≤ (1+2*r)^2+r^2 := by positivity
  have hs := Real.sq_sqrt hs0
  have hn := Real.sqrt_nonneg ((1+2*r)^2+r^2)
  have hlo : 1 ≤ Real.sqrt ((1+2*r)^2+r^2) := by nlinarith
  have hhi : Real.sqrt ((1+2*r)^2+r^2) ≤ 1+3*r := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hhi (by linarith : 0 ≤ 1-r)
  have hmul' := mul_le_mul_of_nonneg_left hlo (by linarith : 0 ≤ 1-r)
  rw [harmonicResponseRatio,abs_of_nonneg (by linarith : 0 ≤ 1-r)]
  apply abs_le.mpr
  constructor <;> nlinarith only [hmul,hmul',hr,sq_nonneg r]

/-- A positive common scale factors exactly out of the actual harmonic
endpoint product. Article: main_krylov, thm:H. -/
theorem harmonic_product_ratio (p r : ℝ) (hp : 0 ≤ p) :
    |p-p*r| * Real.sqrt ((p+2*(p*r))^2+(p*r)^2) = p^2*harmonicResponseRatio r := by
  rw [show p-p*r=p*(1-r) by ring,abs_mul,abs_of_nonneg hp,
    show (p+2*(p*r))^2+(p*r)^2=p^2*((1+2*r)^2+r^2) by ring,
    Real.sqrt_mul (sq_nonneg p),Real.sqrt_sq_eq_abs,abs_of_nonneg hp]
  unfold harmonicResponseRatio
  ring

/-- The native actual-function harmonic RFC coefficient has exactly the
printed one-half constant, its genuine initial step energy and genuine
penultimate error, with an explicit dimensionless ratio multiplier.
Article: main_krylov, thm:H. -/
theorem rfc_harmonic_half_coefficient {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (u : EuclideanSpace ℝ (Fin (k+1))) (hk : 2 ≤ k) (a : ℝ) (ha : 0 ≤ a)
    (hN : referenceAtomCount base hb (cgOperator base u)=k+1) :
    ‖rfcTensorCanonicalCoefficient base hb
      (metricCubicVariation (krylov.Nonlinear.metricCoordinates base hb)
        (referenceHarmonicTensor base hb (cgOperator base u) a)) u‖ =
      (1/2 : ℝ)*a^2*cgEnergy base (cgOperator base u) 0*
        ‖cgCanonicalError base (cgOperator base u) k‖*
        harmonicResponseRatio (‖canonicalCGStep base (cgOperator base u) k‖/
          ‖canonicalCGStep base (cgOperator base u) 0‖) := by
  let s := ‖canonicalCGStep base (cgOperator base u) 0‖
  let t := ‖canonicalCGStep base (cgOperator base u) k‖
  let p := a*s/Real.sqrt 2
  let r := t/s
  have hs : 0 < s := norm_pos_iff.mpr (canonicalCGStep_ne_zero base hb (cgOperator base u) 0
    (fun i hi => cg_nonstagnation base hb (cgOperator base u) i (by rw [hN]; omega)))
  have hp : 0 ≤ p := by dsimp only [p]; positivity
  have hq : a*t/Real.sqrt 2=p*r := by dsimp only [p,r]; field_simp
  have hpsq : p^2=a^2*s^2/2 := by
    dsimp only [p]
    rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [rfc_harmonic_coefficient_norm base hb u hk a hN]
  change t * |p-a*t/Real.sqrt 2| * Real.sqrt ((p+2*(a*t/Real.sqrt 2))^2+(a*t/Real.sqrt 2)^2)=_
  rw [hq,mul_assoc,harmonic_product_ratio p r hp,hpsq,
    cgEnergy_eq_norm_sq base hb,terminal_step_error_norm base hb (cgOperator base u) (by rw [hN])]
  change t*(a^2*s^2/2*harmonicResponseRatio r)=(1/2 : ℝ)*a^2*s^2*t*harmonicResponseRatio r
  ring

end
end krylov.Functions
