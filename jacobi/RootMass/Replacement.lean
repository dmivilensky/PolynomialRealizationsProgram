import jacobi.RootMass.Activity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
The new density replaces m by a nonnegative constant on an actual finite
measurable set, preserving all three integrability requirements. Every
observable's exact integral change is proved before any limiting variation.
Source: measurable indicators and absolutely convergent Lebesgue integral splitting.
Use: implements the admissible needle variations in the original density space.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The literal finite-set replacement function.
Use: implements the admissible needle variations in the original density space.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
-/
def splice (s : Set ℝ) (m : ℝ → ℝ) (z : ℝ) : ℝ → ℝ := s.indicator (fun _ => z)+sᶜ.indicator m

/-- Every observable of the replacement has the exact corresponding measurable-set decomposition.
Use: proves integrability and exact variation formulas for mass, energy and root mass uniformly.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: inside the set the density is z, and outside it is the original m. -/
theorem splice_observable (s : Set ℝ) (m F : ℝ → ℝ) (z : ℝ) :
    (fun x => F (splice s m z x))=s.indicator (fun _ => F z)+sᶜ.indicator (fun x => F (m x)) := by
  classical
  funext x
  by_cases hx : x∈s <;> simp [splice,hx]

/-- Every originally integrable observable stays integrable under a finite-measure constant replacement.
Use: the actual needle competitor has finite root mass and energy, not merely a formal variation.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the replacement observable is a finite-set constant indicator plus the restricted original integrand. -/
theorem splice_integrable {s : Set ℝ} (hs : MeasurableSet s) (hfin : volume s≠⊤)
    {m F : ℝ → ℝ} (hi : Integrable (fun x => F (m x))) (z : ℝ) :
    Integrable (fun x => F (splice s m z x)) := by
  rw [splice_observable]
  exact ((integrableOn_const hfin).integrable_indicator hs).add (hi.indicator hs.compl)

/-- The exact integral difference for every genuinely integrable observable of a finite-set replacement.
Use: derives the three polynomial cost variations used in the actual pointwise minimum principle.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: split both integrals over the measurable set and its complement,
then cancel the unchanged exterior integral. -/
theorem splice_integral {s : Set ℝ} (hs : MeasurableSet s) (hfin : volume s≠⊤)
    {m F : ℝ → ℝ} (hi : Integrable (fun x => F (m x))) (z : ℝ) :
    (∫ x,F (splice s m z x))-(∫ x,F (m x))=∫ x in s,F z-F (m x) := by
  -- All linearity steps use actual integrability, including the finite-set constant.
  rw [splice_observable]
  have hA : (∫ x,s.indicator (fun _ => F z) x+sᶜ.indicator (fun x => F (m x)) x)=
      (∫ x,s.indicator (fun _ => F z) x)+(∫ x,sᶜ.indicator (fun x => F (m x)) x) :=
    integral_add ((integrableOn_const (C := F z) hfin).integrable_indicator hs) (hi.indicator hs.compl)
  change (∫ x,s.indicator (fun _ => F z) x+sᶜ.indicator (fun x => F (m x)) x)-_= _
  have hc : IntegrableOn (fun _ : ℝ => F z) s := integrableOn_const hfin
  rw [hA,integral_indicator hs,integral_indicator hs.compl,integral_sub hc hi.integrableOn]
  have hh := integral_add_compl hs hi
  linarith

/-- The actual admissible finite-set replacement of a finite root-energy density.
Use: the minimizing property applies to a genuine competitor with all domain obligations proved.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
-/
def RootDensity.replace (m : RootDensity) {s : Set ℝ} (hs : MeasurableSet s)
    (hfin : volume s≠⊤) (z : ℝ) (hz : 0≤z) : RootDensity where
  value := splice s m.value z
  measurable := (measurable_const.indicator hs).add (m.measurable.indicator hs.compl)
  nonneg x := add_nonneg (indicator_nonneg (fun _ _ => hz) x) (indicator_nonneg (fun y _ => m.nonneg y) x)
  integrable := splice_integrable (m := m.value) (F := id) hs hfin m.integrable z
  energy_integrable := splice_integrable (m := m.value) (F := fun r => r^(3/2:ℝ)) hs hfin m.energy_integrable z
  root_integrable := splice_integrable (m := m.value) (F := sqrt) hs hfin m.root_integrable z

/-- The original density is recovered by an empty needle interval.
Use: every actual variation has its declared base point at epsilon=0.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: both endpoints of the zero-width half-open interval coincide. -/
theorem splice_zero_interval (m : ℝ → ℝ) (z x : ℝ) : splice (Ioc x (x+0)) m z=m := by
  funext t
  simp [splice]

/-- A right needle has the exact ordinary interval-integral observable variation.
Use: the Lebesgue differentiation theorem supplies all three genuine first-order cost changes.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: use the exact replacement identity, identify the half-open set
integral with the oriented integral at nonnegative width, and integrate the constant. -/
theorem splice_interval_integral {m F : ℝ → ℝ} (hi : Integrable (fun x => F (m x)))
    (z x eps : ℝ) (heps : 0≤eps) :
    (∫ t,F (splice (Ioc x (x+eps)) m z t))=(∫ t,F (m t))+eps*F z-∫ t in x..x+eps,F (m t) := by
  -- The actual replacement interval and the differentiated primitive are exactly the same set modulo endpoints.
  have hh := splice_integral measurableSet_Ioc (by simp) hi z (s := Ioc x (x+eps))
  have hc : IntegrableOn (fun _ : ℝ => F z) (Ioc x (x+eps)) := integrableOn_const (by simp)
  rw [integral_sub hc hi.integrableOn,
    setIntegral_const,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (by linarith : 0≤x+eps-x),
    smul_eq_mul,← intervalIntegral.integral_of_le (by linarith : x≤x+eps)] at hh
  linarith

end
end jacobi.RootMass
