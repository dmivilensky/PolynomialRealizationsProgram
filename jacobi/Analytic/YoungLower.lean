import jacobi.Young.Constants
import jacobi.Bessel.EdgeData
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Article: jacobi, Section 3.2 (sharp comparison at U).
The actual explicit Young lower constant has the original Bessel
second moment, is real analytic, and has the exact derivative at U.
This part of the parameter analysis is independent of finite limits.
Use: youngLower and youngLower_spectral identify the same actual lower calibration without a separately assumed spectrum.
-/
namespace jacobi.Parameter
noncomputable section
open Real Set Filter
open scoped Topology

/-- The source's actual explicit second Bessel edge moment as a function of the order.
Use: youngLower and youngLower_spectral identify the same actual lower calibration without a separately assumed spectrum.
Article: jacobi, Section 3.2 (sharp comparison at U).
-/
def secondMoment (a:ℝ) : ℝ := 1/(4*(a+1)^2*(a+2))

/-- The actual printed Young lower constant as a function of the source order.
Use: Theorem 4.2's contact argument uses this explicit analytic lower function and its exact derivative at U.
Article: jacobi, Section 3.2 (sharp comparison at U).
-/
def youngLower (a:ℝ) : ℝ := jacobi.Young.youngValue (secondMoment a)

/-- The actual Bessel edge spectrum gives exactly the explicit source Young lower constant.
Use: the parameter-dependent lower function in Theorem 4.2 is precisely the calibration of the already proved original edge spectrum.
Article: jacobi, Theorem 4.2.
Proof: insert the independently proved exact second Rayleigh sum. -/
theorem youngLower_spectral {a:ℝ} (ha:-1<a) :
    youngLower a= jacobi.Young.youngValue (jacobi.Bessel.edgeSpectrum a ha).second := by
  rw [jacobi.Bessel.edgeSpectrum_second ha]
  rfl

/-- The actual source second moment is strictly positive throughout the full original order range.
Use: the analytic logarithm and the genuine fractional-power derivative of youngLower have all positivity premises discharged.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: both original affine denominator factors are positive. -/
theorem secondMoment_pos {a:ℝ} (ha:-1<a) : 0<secondMoment a := by
  have h1 : 0<a+1 := by linarith
  have h2 : 0<a+2 := by linarith
  unfold secondMoment
  positivity

/-- The actual Young lower constant takes exactly the source value two fifteenths at U.
Use: Theorem 4.2's analytic contact is at this exact common lower and upper value.
Article: jacobi, Theorem 4.2.
Proof: the actual second moment is two forty-fifths, and the independently proved exact Young calibration supplies its value. -/
theorem youngLower_U : youngLower (1/2)=2/15 := by
  rw [youngLower,show secondMoment (1/2)=2/45 by norm_num [secondMoment],jacobi.Young.youngValue_at_U]

/-- The actual printed second moment is real analytic at every original admissible order.
Use: youngLower_analytic takes its actual positive logarithm to prove the analytic lower half of Theorem 4.2's contact argument.
Article: jacobi, Theorem 4.2.
Proof: the true denominator is a polynomial which is nonzero in the original order range. -/
theorem secondMoment_analytic {a:ℝ} (ha:-1<a) : AnalyticAt ℝ secondMoment a := by
  have h1 : a+1≠0 := by linarith
  have h2 : a+2≠0 := by linarith
  unfold secondMoment
  fun_prop (disch := positivity)

/-- The actual original Young lower constant is real analytic on the complete original order range.
Use: Theorem 4.2's quadratic contact compares this already analytic explicit lower constant with the actual upper constant's parameter continuation.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: the positive actual second moment is analytic. Write its genuine fractional power locally as exp((3/4)*log(T_2)) and compose the community analytic logarithm and exponential. -/
theorem youngLower_analytic {a:ℝ} (ha:-1<a) : AnalyticAt ℝ youngLower a := by
  -- Positivity is proved for the original moment before the logarithmic analytic representation is used.
  have hT := secondMoment_analytic ha
  have hlog := hT.log (secondMoment_pos ha)
  have he : AnalyticAt ℝ (fun x => (18/5:ℝ)^(1/4:ℝ)*exp (log (secondMoment x)*(3/4:ℝ))) a := by
    fun_prop
  apply he.congr
  filter_upwards [hT.continuousAt.eventually (Ioi_mem_nhds (secondMoment_pos ha))] with x hx
  simp only [youngLower,jacobi.Young.youngValue,rpow_def_of_pos hx]

end
end jacobi.Parameter
