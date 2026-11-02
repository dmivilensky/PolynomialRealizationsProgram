import jacobi.Variational.DensityCone
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
Article: jacobi, Lemma D.3.
The cone variational inequality on all actual finite-energy densities
implies nonnegativity of its coefficient and its vanishing on the positive
base density. Testing arbitrary finite-measure indicators proves the
pointwise conclusion with no smooth-test density approximation assumption.
Source: the fundamental lemma for Lebesgue integrals and nonnegative integrands.
Use: all pointwise KKT tests belong to the original article domain.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The indicator of any measurable finite-measure set is an actual finite-energy density.
Use: all pointwise KKT tests belong to the original article domain.
Article: jacobi, Lemma D.3.
-/
def Density.indicator (s : Set ℝ) (hs : MeasurableSet s) (hfin : volume s<∞) : Density where
  value := s.indicator (fun _ => 1)
  measurable := measurable_const.indicator hs
  nonneg x := indicator_nonneg (fun _ _ => zero_le_one) x
  integrable := (integrableOn_const hfin.ne).integrable_indicator hs
  energy_integrable := by
    have he : (fun x => (s.indicator (fun _ : ℝ => (1:ℝ)) x)^(3/2:ℝ))=
        s.indicator (fun _ : ℝ => (1:ℝ)) := by
      funext x
      by_cases hx : x∈s <;> simp [hx,Real.zero_rpow (by norm_num : (3/2:ℝ)≠0)]
    rw [he]
    exact (integrableOn_const hfin.ne).integrable_indicator hs

/-- Cone stationarity forces nonnegativity and complementary vanishing of its actual pointwise coefficient.
Use: turns the proved normal multiplier variational inequality into sqrt(m)=(2/3)*(mu*gamma-lambda)_+.
Article: jacobi, Lemma D.3.
Proof: adding any density to m gives a nonnegative integral against that
density. Finite-measure indicator tests then imply Psi>=0 a.e. The zero
competitor gives integral Psi*m<=0; nonnegativity makes that integral zero
and forces its nonnegative integrand to vanish a.e. -/
theorem density_cone_complementarity (m : Density) (ψ : ℝ → ℝ)
    (hi : ∀ q : Density,Integrable (fun x => ψ x*q.value x))
    (hvar : ∀ q : Density,0≤∫ x,ψ x*(q.value x-m.value x)) :
    (∀ᵐ x : ℝ,0≤ψ x) ∧ (fun x => ψ x*m.value x)=ᵐ[volume] 0 := by
  -- The full density cone contains every positive additive test, so no test-function density lemma is assumed.
  have htest (q : Density) : 0≤∫ x,ψ x*q.value x := by
    have he : (fun x => ψ x*((m.add q).value x-m.value x))=fun x => ψ x*q.value x := by
      funext x
      change ψ x*(m.value x+q.value x-m.value x)=_
      ring
    simpa only [he] using hvar (m.add q)
  have hind (s : Set ℝ) (hs : MeasurableSet s) (hfin : volume s<∞) :
      IntegrableOn ψ s ∧ 0≤∫ x in s,ψ x := by
    let q := Density.indicator s hs hfin
    have he : (fun x => ψ x*q.value x)=s.indicator ψ := by
      funext x
      by_cases hx : x∈s <;> simp [q,Density.indicator,hx]
    have hin := hi q
    have hnon := htest q
    rw [he] at hin hnon
    exact ⟨(integrable_indicator_iff hs).mp hin,by rwa [integral_indicator hs] at hnon⟩
  have hψ : ∀ᵐ x : ℝ,0≤ψ x :=
    ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
      (fun s hs hfin => (hind s hs hfin).1) (fun s hs hfin => (hind s hs hfin).2)
  refine ⟨hψ,?_⟩
  have hψm : ∀ᵐ x : ℝ,0≤ψ x*m.value x := hψ.mono fun x hx => mul_nonneg hx (m.nonneg x)
  have hz := hvar (m.scale 0 le_rfl)
  have he : (fun x => ψ x*((m.scale 0 le_rfl).value x-m.value x))=fun x => -(ψ x*m.value x) := by
    funext x
    change ψ x*(0*m.value x-m.value x)=_
    ring
  rw [he,integral_neg] at hz
  have hint : (∫ x,ψ x*m.value x)=0 :=
    le_antisymm (by linarith) (integral_nonneg_of_ae hψm)
  exact (integral_eq_zero_iff_of_nonneg_ae hψm (hi m)).mp hint

/-- Pointwise cone complementarity is exactly the positive-part Euler equation of the article.
Use: completes the normal multiplier rule once its variational inequality has been derived.
Article: jacobi, Lemma D.3.
Proof: on m>0 the complementary coefficient must vanish; on m=0 its
nonnegativity makes the positive part zero. Both alternatives are purely pointwise. -/
theorem positivePart_of_complementarity (m : Density) (γ : ℝ → ℝ) (μ l : ℝ)
    (hn : ∀ᵐ x : ℝ,0≤(3/2:ℝ)*sqrt (m.value x)+l-μ*γ x)
    (hz : (fun x => ((3/2:ℝ)*sqrt (m.value x)+l-μ*γ x)*m.value x)=ᵐ[volume] 0) :
    (fun x => sqrt (m.value x))=ᵐ[volume] fun x => (2/3:ℝ)*max (μ*γ x-l) 0 := by
  -- The density's nonnegative branch and the pointwise cone coefficient determine each case.
  filter_upwards [hn,hz] with x hn hz
  by_cases hm : m.value x=0
  · rw [hm,sqrt_zero,mul_zero,zero_add] at hn
    rw [hm,sqrt_zero,max_eq_right (by linarith)]
    ring
  · have hc : (3/2:ℝ)*sqrt (m.value x)+l-μ*γ x=0 := (mul_eq_zero.mp hz).resolve_right hm
    have hp : 0≤μ*γ x-l := by linarith [sqrt_nonneg (m.value x)]
    rw [max_eq_left hp]
    linarith

end
end jacobi.Variational
