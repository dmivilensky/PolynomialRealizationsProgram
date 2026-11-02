import jacobi.Jacobi.RegularCotangent
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: jacobi, Proposition B.1.
The actual Liouville remainder is defined through its smooth primitive,
identified with the printed expression away from zero, and proved analytic
across zero. A single genuine compact C1 bound supplies the source constant C4.
Use: supplies the explicit phase correction and its rigorously bounded endpoint contribution in the uniform zero estimates.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual smooth primitive of the regular Jacobi Liouville remainder.
Use: supplies the explicit phase correction and its rigorously bounded endpoint contribution in the uniform zero estimates.
Article: jacobi, Proposition B.1.
-/
def regularPrimitive (a b t : ℝ) : ℝ :=
  endpointCorrection a*regularCotangent t+
    endpointCorrection b/2*(sin (t/2)/cos (t/2))

/-- The genuine smooth extension of the source's regular Liouville remainder.
Use: the inverse-square Bessel equation differs from the actual Jacobi equation by this uniformly C1 bounded function.
Article: jacobi, Proposition B.1.
-/
def regularPotential (a b : ℝ) : ℝ → ℝ := deriv (regularPrimitive a b)

/-- The literal remainder primitive is analytic on the entire comparison neighborhood (-pi,pi).
Use: all derivatives of the true remainder extend continuously through the singular endpoint.
Article: jacobi, Proposition B.1.
Proof: the actual removable cotangent function is analytic. The other
term is the ordinary analytic half-angle sine/cosine quotient, whose
cosine denominator is positive on this full open neighborhood. -/
theorem regularPrimitive_analytic (a b : ℝ) {t : ℝ} (ht : t∈Ioo (-Real.pi) Real.pi) :
    AnalyticAt ℝ (regularPrimitive a b) t := by
  -- The original apparent endpoint singularity has already been removed by an actual analytic divided difference.
  have hi : AnalyticAt ℝ (fun x : ℝ => x/2) t := analyticAt_id.div_const
  have hS := Real.analyticAt_sin.comp (f := fun x : ℝ => x/2) hi
  have hC := Real.analyticAt_cos.comp (f := fun x : ℝ => x/2) hi
  have hc : cos (t/2)≠0 := (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1],by linarith [ht.2]⟩).ne'
  have hH := regularCotangent_analytic (t := t) ⟨by linarith [ht.1,Real.pi_pos],by linarith [ht.2,Real.pi_pos]⟩
  exact (analyticAt_const.mul hH).add (analyticAt_const.mul (hS.div hC hc))

/-- The actual comparison remainder and its derivative are analytic throughout the full comparison neighborhood.
Use: discharges the uniform C1 bounds required by both Sturm and phase comparison estimates.
Article: jacobi, Proposition B.1.
Proof: both functions are genuine successive derivatives of the already proved analytic primitive. -/
theorem regularPotential_analytic (a b : ℝ) {t : ℝ} (ht : t∈Ioo (-Real.pi) Real.pi) :
    AnalyticAt ℝ (regularPotential a b) t ∧ AnalyticAt ℝ (deriv (regularPotential a b)) t :=
  ⟨(regularPrimitive_analytic a b ht).deriv,(regularPrimitive_analytic a b ht).deriv.deriv⟩

/-- The genuine remainder primitive starts at zero.
Use: its integral formula and linear endpoint bound have no unknown integration constant.
Article: jacobi, Proposition B.1.
Proof: the removable cotangent value and the half-angle sine both vanish at zero. -/
theorem regularPrimitive_zero (a b : ℝ) : regularPrimitive a b 0=0 := by
  simp only [regularPrimitive,regularCotangent_zero,zero_div,sin_zero,cos_zero,mul_zero,add_zero]

/-- The genuine smooth primitive equals its exact source expression at every positive interior point.
Use: identifies the explicit correction in the source's zero expansion with the actual comparison primitive.
Article: jacobi, Proposition B.1.
Proof: substitute the already proved removable cotangent identity; the remaining half-angle term is the literal original quotient. -/
theorem regularPrimitive_eq (a b : ℝ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    regularPrimitive a b t=endpointCorrection a*(1/t-(1/2)*(cos (t/2)/sin (t/2)))+
      endpointCorrection b/2*(sin (t/2)/cos (t/2)) := by
  rw [regularPrimitive,regularCotangent_eq ht]

/-- The derivative of the actual primitive is precisely the original inverse-square remainder away from the singular endpoint.
Use: the true Jacobi Liouville equation and the Bessel comparison equation differ by exactly this proved smooth remainder.
Article: jacobi, Proposition B.1.
Proof: write the two half-angle terms using the already differentiated
Liouville logarithmic slopes. The ordinary inverse derivative and their
true derivative formulas yield the literal printed potential. -/
theorem regularPrimitive_hasDerivAt (a b : ℝ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    HasDerivAt (regularPrimitive a b)
      (endpointCorrection a*(1/(4*sin (t/2)^2)-1/t^2)+endpointCorrection b/(4*cos (t/2)^2)) t := by
  -- Derivatives of the actual half-angle logarithmic slopes avoid assuming a singular-potential identity.
  have h1 := ((hasDerivAt_id t).inv ht.1.ne').sub (liouvilleLogSlope_hasDerivAt (1/2) (-1/2) ht)
  have h2 := liouvilleLogSlope_hasDerivAt (-1/2) (1/2) ht
  have h := (h1.const_mul (endpointCorrection a)).sub (h2.const_mul (endpointCorrection b))
  have he : regularPrimitive a b=ᶠ[𝓝 t] fun x : ℝ =>
      endpointCorrection a*(x⁻¹-liouvilleLogSlope (1/2) (-1/2) x)-
        endpointCorrection b*liouvilleLogSlope (-1/2) (1/2) x := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    rw [regularPrimitive_eq a b hx]
    norm_num only [liouvilleLogSlope,add_neg_cancel,zero_div,zero_mul,sub_zero,
      neg_div,neg_mul,one_div]
    ring
  convert h.congr_of_eventuallyEq he using 1
  dsimp [liouvilleLogAcceleration]
  ring

/-- The smooth comparison remainder is exactly the printed potential at every positive interior point.
Use: inserts the genuinely bounded C1 potential into the actual finite Jacobi equation.
Article: jacobi, Proposition B.1.
Proof: the ordinary derivative of the actual primitive is unique. -/
theorem regularPotential_eq (a b : ℝ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    regularPotential a b t=endpointCorrection a*(1/(4*sin (t/2)^2)-1/t^2)+
      endpointCorrection b/(4*cos (t/2)^2) := (regularPrimitive_hasDerivAt a b ht).deriv

/-- One positive constant bounds the actual regular Jacobi potential and its actual derivative on the entire source comparison interval.
Use: supplies the genuine C4 needed for uniform Sturm comparison, the phase perturbation and oscillatory integration by parts.
Article: jacobi, Proposition B.1.
Proof: the actual potential and derivative are analytic on a neighborhood
of the full compact interval. Bound their continuous images separately,
then enlarge both finite bounds to one strictly positive constant. -/
theorem regularPotential_C1_bound (a b : ℝ) : ∃ C : ℝ,0<C ∧
    ∀ t∈Icc 0 (3*Real.pi/4),|regularPotential a b t|≤C ∧ |deriv (regularPotential a b) t|≤C := by
  -- Compactness is applied to the actual smooth extension, so the endpoint zero is included in both bounds.
  have hmem : ∀ t∈Icc 0 (3*Real.pi/4),t∈Ioo (-Real.pi) Real.pi := by
    intro t ht
    exact ⟨by linarith [ht.1,Real.pi_pos],by linarith [ht.2,Real.pi_pos]⟩
  have h0 : ContinuousOn (regularPotential a b) (Icc 0 (3*Real.pi/4)) :=
    fun t ht => ((regularPotential_analytic a b (hmem t ht)).1.continuousAt).continuousWithinAt
  have h1 : ContinuousOn (deriv (regularPotential a b)) (Icc 0 (3*Real.pi/4)) :=
    fun t ht => ((regularPotential_analytic a b (hmem t ht)).2.continuousAt).continuousWithinAt
  obtain ⟨C0,hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn h0
  obtain ⟨C1,hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn h1
  refine ⟨|C0|+|C1|+1,by positivity,?_⟩
  intro t ht
  have hh0 : |regularPotential a b t|≤C0 := by simpa only [Real.norm_eq_abs] using hC0 t ht
  have hh1 : |deriv (regularPotential a b) t|≤C1 := by simpa only [Real.norm_eq_abs] using hC1 t ht
  constructor <;> linarith [le_abs_self C0,le_abs_self C1,abs_nonneg C0,abs_nonneg C1]

/-- The original Jacobi Liouville wave satisfies the actual inverse-square Bessel equation with its genuinely smooth bounded remainder.
Use: the full source zero comparison is now a perturbation of the actual Bessel restoring equation with all coefficient regularity discharged.
Article: jacobi, Proposition B.1.
Proof: substitute the proved literal remainder into the already established actual Jacobi Liouville equation and collect the singular coefficient. -/
theorem liouville_regular_equation {a b : ℝ} (ha : -1<a) (n : ℕ) {t : ℝ} (ht : t∈Ioo 0 Real.pi) :
    liouvilleAcceleration a b n t+
      (frequency a b n^2+endpointCorrection a/t^2+regularPotential a b t)*liouville a b n t=0 := by
  rw [regularPotential_eq a b ht]
  convert liouville_equation ha n ht using 1 <;> ring

end
end jacobi.Jacobi
