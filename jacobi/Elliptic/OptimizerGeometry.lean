import jacobi.Elliptic.PhaseGeometry
import jacobi.Elliptic.MassSaturation
import jacobi.Young.RadialPotential

/-!
Article: jacobi, Theorem D.5.
The genuine attained optimizer has an even normalized state, its unique
peak at zero, strictly negative slope on the positive half-line, and a
finite positive core. Its actual multipliers and turning parameter are
constructed from minimality. These are the geometric hypotheses needed
for the mass, second-moment and energy quadrature substitution.
Source: the proved normal Euler equation and clipped phase-plane geometry.
Use: fixes the turning point in the article's centered elliptic profile.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Filter Set jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized radial Euler state is even and has zero slope at the origin.
Use: fixes the turning point in the article's centered elliptic profile.
Article: jacobi, Theorem D.5.
Proof: symmetry of the actual potential gives symmetry of y; differentiate
its reflection at zero and use uniqueness of the scalar derivative. -/
theorem eulerState_even (m : Density) (hs : SymmetricDecreasing m.value) (μ l : ℝ) :
    (∀ x,eulerState m μ l (-x)=eulerState m μ l x) ∧ eulerSlope m μ 0=0 := by
  -- The zero central slope is proved from the actual derivative, not imposed as initial data.
  have he (x : ℝ) : eulerState m μ l (-x)=eulerState m μ l x := by
    unfold eulerState
    rw [potential_even m hs]
  have href := (eulerState_hasDerivAt m μ l (-0)).comp 0 (hasDerivAt_neg (0:ℝ))
  have hder : HasDerivAt (eulerState m μ l) (-eulerSlope m μ 0) 0 := by
    simpa only [Function.comp_def,he,neg_zero,mul_neg_one] using href
  have hh := hder.unique (eulerState_hasDerivAt m μ l 0)
  exact ⟨he,by linarith⟩

/-- The actual elliptic Euler state always lies strictly above its negative limiting shift.
Use: the turning cubic has no additional accessible critical root in the actual phase trajectory.
Article: jacobi, Theorem D.5.
Proof: the actual potential of a positive-mass source is strictly positive and the scaling factor is positive. -/
theorem eulerState_gt_shift (m : Density) (hm : 0<m.mass) {μ : ℝ} (hμ : 0<μ) (l x : ℝ) :
    eulerShift μ l<eulerState m μ l x := by
  have ha := eulerScale_pos hμ
  have hp := potential_pos m hm x
  unfold eulerState eulerShift
  apply (div_lt_div_iff_of_pos_right ha).mpr
  nlinarith

/-- The actual radial negative-shift Euler solution has its forced turning point and strict slope at the origin.
Use: supplies the full actual descending branch for the elliptic quadrature identities.
Article: jacobi, Theorem D.5.
Proof: attain a positive maximum by two-sided decay. The strict cubic
factorization forces the zero central slope to have that same maximum
value. Apply the proved no-second-turning and negative-slope theorem. -/
theorem eulerState_peak (m : Density) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    {μ l : ℝ} (hμ : 0<μ) (hl : 0<l) (he : m.value=ᵐ[volume] eulerDensity m μ l) :
    1≤eulerState m μ l 0 ∧
      (eulerState m μ l 0-eulerShift μ l)^2=(eulerState m μ l 0)^3 ∧
      (∀ x,eulerState m μ l x≤eulerState m μ l 0) ∧
      ∀ x,0<x → eulerSlope m μ x<0 := by
  -- All phase-plane hypotheses come from this actual optimizer and its actual potential.
  have hσ : eulerShift μ l<0 := by unfold eulerShift; exact div_neg_of_neg_of_pos (neg_neg_of_pos hl) (eulerScale_pos hμ)
  have h0 := (eulerState_even m hs μ l).2
  obtain ⟨b,hY,hdb,hroot,hmax⟩ := clipped_turning_height hσ.le (eulerState_hasDerivAt m μ l)
    (eulerState_equation m hμ l he) (eulerState_integrable m μ l).1
    (eulerState_integrable m μ l).2 (eulerState_positiveCube_integrable m hμ l he)
    (eulerState_limits m μ l).1 (eulerState_limits m μ l).2
    (eulerState_positive_point m hm hμ l he)
  have heq : eulerState m μ l 0=eulerState m μ l b := by
    apply le_antisymm (hmax 0)
    by_contra! hlt
    have hp := turning_polynomial_pos hY hroot (eulerState_gt_shift m hm hμ l 0) hlt
    have hw := eulerState_first_integral m hμ l he 0
    rw [h0] at hw
    nlinarith
  rw [← heq] at hY hroot hmax
  refine ⟨hY,hroot,hmax,fun x hx => ?_⟩
  exact clipped_slope_neg hσ (eulerState_hasDerivAt m μ l) (eulerState_equation m hμ l he)
    (eulerState_first_integral m hμ l he) hY h0 hroot hmax
    (eulerState_gt_shift m hm hμ l) (eulerState_limits m μ l).1 hx

/-- The actual elliptic Euler state is strictly decreasing on the closed positive half-line.
Use: identifies its positive core as one interval and its state map as injective for substitution.
Article: jacobi, Theorem D.5.
Proof: the actual derivative is strictly negative at every interior point of the half-line. -/
theorem eulerState_strictAnti (m : Density) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    {μ l : ℝ} (hμ : 0<μ) (hl : 0<l) (he : m.value=ᵐ[volume] eulerDensity m μ l) :
    StrictAntiOn (eulerState m μ l) (Ici 0) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0)
    (continuous_iff_continuousAt.mpr fun x => (eulerState_hasDerivAt m μ l x).continuousAt).continuousOn
    (fun x _ => (eulerState_hasDerivAt m μ l x).hasDerivWithinAt)
  intro x hx
  exact (eulerState_peak m hm hs hμ hl he).2.2.2 x (by simpa only [interior_Ici,mem_Ioi] using hx)

/-- The actual negative-shift optimizer has a finite positive core with two exact free boundaries.
Use: the positive descending branch is a finite interval for the exact quadrature substitution.
Article: jacobi, Theorem D.5.
Proof: the strictly decreasing even state starts positive and tends to its
negative shift. The intermediate value theorem gives its unique positive
zero; strict monotonicity characterizes the entire positive set. -/
theorem eulerState_positive_core (m : Density) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    {μ l : ℝ} (hμ : 0<μ) (hl : 0<l) (he : m.value=ᵐ[volume] eulerDensity m μ l) :
    ∃ a : ℝ,0<a ∧ eulerState m μ l a=0 ∧
      ∀ x,(0<eulerState m μ l x ↔ |x|<a) := by
  -- A negative endpoint limit forces an actual finite crossing of the strictly descending state.
  have hσ : eulerShift μ l<0 := by unfold eulerShift; exact div_neg_of_neg_of_pos (neg_neg_of_pos hl) (eulerScale_pos hμ)
  have hneg := (eulerState_limits m μ l).1.eventually (Iio_mem_nhds hσ)
  obtain ⟨R,hR,hfR⟩ := (eventually_gt_atTop (0:ℝ)).and hneg |>.exists
  have hc : Continuous (eulerState m μ l) :=
    continuous_iff_continuousAt.mpr fun x => (eulerState_hasDerivAt m μ l x).continuousAt
  have hpeak := (eulerState_peak m hm hs hμ hl he).1
  obtain ⟨a,ha,hfa⟩ := (intermediate_value_Icc' hR.le hc.continuousOn)
    ⟨hfR.le,(by linarith : 0≤eulerState m μ l 0)⟩
  have ha0 : 0<a := lt_of_le_of_ne ha.1 (by
    intro hz
    rw [← hz] at hfa
    linarith)
  have hanti := eulerState_strictAnti m hm hs hμ hl he
  have habs (x : ℝ) : eulerState m μ l |x|=eulerState m μ l x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx,(eulerState_even m hs μ l).1]
  refine ⟨a,ha0,hfa,fun x => ?_⟩
  rw [← habs x]
  constructor
  · intro hp
    by_contra! hx
    have hh := hanti.antitoneOn ha0.le (abs_nonneg x) hx
    rw [hfa] at hh
    linarith
  · intro hx
    have hh := hanti (abs_nonneg x) ha0.le hx
    rwa [hfa] at hh

/-- Every actual elliptic-regime attainer has the printed interior turning parameter and finite-core state.
Use: starts the exact elliptic calibration from a proved actual minimizer with no assumed ODE or shape data.
Article: jacobi, Theorem D.5.
Proof: actual KKT and mass saturation construct positive multipliers.
The actual zero first integral gives the peak equation; its negative shift
fixes t in (0,1). The proved profile geometry gives the finite positive core. -/
theorem elliptic_optimizer_geometry {M T : ℝ} (hT : 0<T) (hregime : 2*M^2<5*T)
    (m : Density) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    (hmM : m.mass≤M) (hmT : T≤observe m .second)
    (hmin : m.cost=relaxedInfimum {Observation.second} M (fun _ => T)) :
    m.mass=M ∧ observe m .second=T ∧
      ∃ μ l t a : ℝ,0<μ ∧ 0<l ∧ t∈Ioo (0:ℝ) 1 ∧ 0<a ∧
        m.value=ᵐ[volume] eulerDensity m μ l ∧
        eulerState m μ l 0=(t⁻¹)^2 ∧ eulerShift μ l=(t⁻¹)^2-(t⁻¹)^3 ∧
        eulerState m μ l a=0 ∧ (∀ x,0<eulerState m μ l x ↔ |x|<a) ∧
        ∀ x,0<x → eulerSlope m μ x<0 := by
  -- Every returned parameter belongs to the same actual attained variational optimizer.
  obtain ⟨hM,μ,l,hμ,hl,he⟩ := elliptic_mass_saturation hT hregime m hm hs hmM hmT hmin
  obtain ⟨hY,hroot,_,hslope⟩ := eulerState_peak m hm hs hμ hl he
  have hσ : eulerShift μ l<0 := by unfold eulerShift; exact div_neg_of_neg_of_pos (neg_neg_of_pos hl) (eulerScale_pos hμ)
  obtain ⟨t,ht,ht1,hYt,hσt⟩ := turning_shape_parameter hY hσ hroot
  obtain ⟨a,ha,hzero,hcore⟩ := eulerState_positive_core m hm hs hμ hl he
  exact ⟨hM,(second_minimizer_kkt hT m hm hs hmM hmT hmin).1,
    μ,l,t,a,hμ,hl,⟨ht,ht1⟩,ha,he,hYt,hσt,hzero,hcore,hslope⟩

end
end jacobi.Elliptic
