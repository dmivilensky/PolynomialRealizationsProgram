import polyak.ModeLocking.Localization.Potential
import Mathlib.Analysis.Calculus.LHopital

/-! Exact second-order coefficients of the locking potential at every atom. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels Filter Set
open scoped Topology BigOperators

theorem analytic_quadratic_limit {f : ℝ → ℝ} {z : ℝ} (hf : AnalyticAt ℝ f z)
    (hfz : f z = 0) (hdfz : deriv f z = 0) :
    Tendsto (fun x => f x / (x-z)^2) (𝓝[≠] z)
      (𝓝 (deriv (deriv f) z / 2)) := by
  have hne : ∀ᶠ x in 𝓝[≠] z, x-z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact sub_ne_zero.mpr hx
  have hd : ∀ᶠ x in 𝓝[≠] z, HasDerivAt f (deriv f x) x :=
    (hf.eventually_analyticAt.mono fun x hx => hx.differentiableAt.hasDerivAt).filter_mono
      nhdsWithin_le_nhds
  have hg : ∀ᶠ x in 𝓝[≠] z,
      HasDerivAt (fun x : ℝ => (x-z)^2) (2*(x-z)) x :=
    Filter.Eventually.of_forall fun x => by
      convert ((hasDerivAt_id x).sub_const z).pow 2 using 1
      · funext y
        rfl
      · norm_num [id_eq]
  have hratio : Tendsto (fun x => deriv f x/(x-z)) (𝓝[≠] z) (𝓝 (deriv (deriv f) z)) := by
    have hh := hf.deriv.differentiableAt.hasDerivAt.tendsto_slope
    change Tendsto (fun x => slope (deriv f) z x) _ _ at hh
    simpa only [slope_def_field,hdfz,sub_zero] using hh
  have hr : Tendsto (fun x => deriv f x/(2*(x-z))) (𝓝[≠] z)
      (𝓝 (deriv (deriv f) z/2)) := by
    convert hratio.div_const 2 using 1
    ext x
    rw [mul_comm (2:ℝ), div_mul_eq_div_div]
  apply HasDerivAt.lhopital_zero_nhdsNE hd hg
    (hne.mono fun x hx => mul_ne_zero (by norm_num) hx)
  · simpa only [hfz] using hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · have hh : Continuous (fun x : ℝ => (x-z)^2) := by fun_prop
    have hht : Tendsto (fun x : ℝ => (x-z)^2) (𝓝[≠] z) (𝓝 ((z-z)^2)) :=
      hh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [sub_self,zero_pow (by norm_num : 2 ≠ 0)] using hht
  · exact hr

variable {q : General.Tuning} {t : ℝ} {L : ℕ}

def extendedPotential (D : RegularData q t L) (x : ℝ) : ℝ :=
  -finiteSymbol q t D.lags D.dual x /
    (Real.sin (Geometry.jointAngle ![q.kappa,q.y,q.beta,t,x]) * pinningPolynomial D.lags D.dual x)

theorem extendedPotential_actual (D : RegularData q t L) (ω : Frequency) :
    extendedPotential D ω = regularPotential D ω := by
  unfold extendedPotential regularPotential
  rw [Geometry.jointAngle_actual q t ω.property]
  rfl

theorem potential_quadratic_limit (D : RegularData q t L) (i : Fin D.d) :
    Tendsto (fun x => extendedPotential D x / (x-(D.atoms i:ℝ))^2)
      (𝓝[≠] (D.atoms i:ℝ))
      (𝓝 (|deriv^[2] (finiteSymbol q t D.lags D.dual) (D.atoms i:ℝ)| /
        (2*Real.sin (Geometry.shiftedCurve q t (D.atoms i))*
          pinningPolynomial D.lags D.dual (D.atoms i)))) := by
  let z : ℝ := D.atoms i
  have hf := analyticAt_finiteSymbol q t D.lags D.dual (D.atoms i).property
  have hlim := analytic_quadratic_limit hf (D.symbol_zero_support i) (D.symbol_slope_support i)
  have ht : ContinuousAt (fun x : ℝ => Real.sin (Geometry.jointAngle ![q.kappa,q.y,q.beta,t,x])) z := by
    have hp : AnalyticAt ℝ (fun x : ℝ => ![q.kappa,q.y,q.beta,t,x]) z := by
      apply AnalyticAt.pi
      intro j
      fin_cases j
      all_goals first | exact analyticAt_const | exact analyticAt_id
    exact (Real.continuous_sin.continuousAt.comp
      ((Geometry.analyticAt_jointAngle_actual q t (D.atoms i).property).comp (f := fun x : ℝ => ![q.kappa,q.y,q.beta,t,x]) hp).continuousAt)
  have hP : Continuous (pinningPolynomial D.lags D.dual) := by
    unfold pinningPolynomial
    fun_prop
  have he : Geometry.jointAngle ![q.kappa,q.y,q.beta,t,z] = Geometry.shiftedCurve q t (D.atoms i) :=
    Geometry.jointAngle_actual q t (D.atoms i).property
  have hden : Real.sin (Geometry.jointAngle ![q.kappa,q.y,q.beta,t,z]) *
      pinningPolynomial D.lags D.dual z ≠ 0 := by
    rw [he]
    exact (mul_pos (phase_sin_pos q t (D.atoms i)
      ⟨(D.atoms_grid i).1,D.atoms_lt_pi i⟩) (D.pinning_pos i)).ne'
  have hresult := hlim.neg.div ((ht.mul hP.continuousAt).tendsto.mono_left nhdsWithin_le_nhds) hden
  have hneg : |deriv^[2] (finiteSymbol q t D.lags D.dual) z| =
      -deriv (deriv (finiteSymbol q t D.lags D.dual)) z := by
    rw [abs_of_neg (D.support_curvature i)]
    rfl
  change Tendsto (fun x => -(finiteSymbol q t D.lags D.dual x / (x-z)^2) /
    (Real.sin (Geometry.jointAngle ![q.kappa,q.y,q.beta,t,x])*pinningPolynomial D.lags D.dual x))
    (𝓝[≠] z) (𝓝 (-(deriv (deriv (finiteSymbol q t D.lags D.dual)) z / 2) /
      (Real.sin (Geometry.jointAngle ![q.kappa,q.y,q.beta,t,z])*pinningPolynomial D.lags D.dual z))) at hresult
  rw [he] at hresult
  rw [hneg]
  convert hresult using 1
  · ext x
    unfold extendedPotential
    ring
  · congr 1
    dsimp [z]
    ring

end polyak.ModeLocking.Localization
