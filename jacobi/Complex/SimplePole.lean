import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: the elementary simple-pole residue formula, proved here from
analytic divided differences and the community power-series theorem.
Use: simplePole_remainder_analytic removes the original characteristic's simple pole without assuming a Laurent-series or residue theorem.
-/
namespace jacobi.Complex
noncomputable section
open _root_.Complex Set Filter
open scoped Topology

/-- An analytic complex function has an analytic divided difference at the base point itself.
Use: simplePole_remainder_analytic removes the original characteristic's simple pole without assuming a Laurent-series or residue theorem.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: the removable divided-difference theorem for analytic functions.
Proof: shift the genuine local power series by one coefficient using the community dslope power-series theorem. -/
theorem analyticAt_dslope {f : ℂ → ℂ} {p : ℂ} (hf : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (dslope f p) p := by
  obtain ⟨P,hP⟩ := hf
  exact ⟨P.fslope,hP.has_fpower_series_dslope_fslope⟩

/-- The genuine numerator after removing the denominator's simple linear zero.
Use: simplePole_principal_part identifies its value at the pole with g(p)/h'(p), and simplePole_remainder_analytic proves analytic removal of that principal part.
Article: jacobi, Appendix C.2 (exact parity splitting).
-/
def simplePoleNumerator (g h : ℂ → ℂ) (p : ℂ) (z : ℂ) : ℂ :=
  g z/dslope h p z

/-- Subtracting the genuine simple-pole principal part leaves the divided difference of the regular numerator.
Use: finitePoleRegularization_eq_near patches the original meromorphic quotient at every actual pole before applying Cauchy--Goursat.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: h(z)=(z-p)*dslope(h,p,z) when h(p)=0. The numerator's own divided-difference identity gives the exact principal-part subtraction. -/
theorem simplePole_principal_part (g h : ℂ → ℂ) {p z : ℂ}
    (hp : h p=0) (hz : z≠p) :
    g z/h z-(g p/deriv h p)/(z-p)=dslope (simplePoleNumerator g h p) p z := by
  -- All identities are exact for the original totalized complex quotient, without assuming nonzero nearby values of h.
  have he : (z-p)*dslope h p z=h z := by
    simpa only [smul_eq_mul,hp,sub_zero] using sub_smul_dslope h p z
  have hdiv : g z/h z=simplePoleNumerator g h p z/(z-p) := by
    rw [← he,simplePoleNumerator,div_div,mul_comm (dslope h p z) (z-p)]
  rw [hdiv,dslope_of_ne _ hz,slope,smul_eq_mul]
  simp only [simplePoleNumerator,dslope_same,vsub_eq_sub]
  ring

/-- The genuine simple-pole numerator is analytic near the pole, and its principal-part remainder is analytic there as well.
Use: finitePoleRegularization_analytic supplies the local analytic patches in the finite-pole residue theorem applied to the original characteristics.
Article: jacobi, Appendix C.2 (exact parity splitting).
Source: the standard simple-pole removal formula, from analytic divided differences.
Proof: the characteristic's divided difference is analytic and has nonzero value h'(p). Its quotient with g is analytic, and taking one further divided difference preserves analyticity. -/
theorem simplePole_remainder_analytic {g h : ℂ → ℂ} {p : ℂ}
    (hg : AnalyticAt ℂ g p) (hh : AnalyticAt ℂ h p) (hd : deriv h p≠0) :
    AnalyticAt ℂ (simplePoleNumerator g h p) p ∧
      AnalyticAt ℂ (dslope (simplePoleNumerator g h p) p) p := by
  have hc := analyticAt_dslope hh
  have hn : dslope h p p≠0 := by simpa only [dslope_same] using hd
  have hu : AnalyticAt ℂ (simplePoleNumerator g h p) p := hg.div hc hn
  exact ⟨hu,analyticAt_dslope hu⟩

end
end jacobi.Complex
