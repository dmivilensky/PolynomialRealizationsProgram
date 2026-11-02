import jacobi.Elliptic.OptimizerGeometry
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
Article: jacobi, Theorem D.5.
The actual optimizer state supplies a genuine injective differentiable
change of variables on its finite positive half-core. Its zero first
integral and negative slope give the exact square-root Jacobian. Reflection
and the vanishing positive-part integrands recover the whole-line integrals.
Source: the one-dimensional Lebesgue change-of-variables theorem in mathlib.
Use: supplies the mass, energy, second-moment and root-mass identities from the actual attained profile.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Filter Set jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The exact whole-line quadrature of every positive-core observable of the actual elliptic optimizer.
Use: supplies the mass, energy, second-moment and root-mass identities from the actual attained profile.
Article: jacobi, Theorem D.5.
Proof: strict monotonicity maps the open positive half-core bijectively to
(0,y_0). Apply the genuine Jacobian theorem; the first integral makes its
absolute derivative twice sqrt(P). Evenness doubles this half-core integral,
while the observable vanishes outside the positive core. -/
theorem eulerState_quadrature (m : Density) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    {μ l : ℝ} (hμ : 0<μ) (hl : 0<l) (he : m.value=ᵐ[volume] eulerDensity m μ l)
    (F : ℝ → ℝ) (hF : ∀ v,v≤0 → F v=0) :
    (∫ x,F (eulerState m μ l x))=
      ∫ v in Ioo (0:ℝ) (eulerState m μ l 0),
        F v/sqrt ((v-eulerShift μ l)^2-v^3) := by
  -- Use the actual state and its actual finite core in the change of variables.
  let f := eulerState m μ l
  let d := eulerSlope m μ
  let σ := eulerShift μ l
  obtain ⟨a,ha,hzero,hcore⟩ := eulerState_positive_core m hm hs hμ hl he
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (eulerState_hasDerivAt m μ l x).continuousAt
  have hanti := eulerState_strictAnti m hm hs hμ hl he
  have hmaps : f '' Ioo (0:ℝ) a=Ioo (0:ℝ) (f 0) := by
    have hh := hc.continuousOn.image_Ioo_of_strictAntiOn ha.le
      (hanti.mono (show Icc (0:ℝ) a⊆Ici 0 from fun _ hx => hx.1))
    change f a=0 at hzero
    rwa [hzero] at hh
  have hder (x : ℝ) (_hx : x∈Ioo (0:ℝ) a) : HasDerivWithinAt f (d x) (Ioo (0:ℝ) a) x :=
    (eulerState_hasDerivAt m μ l x).hasDerivWithinAt
  have hinj : InjOn f (Ioo (0:ℝ) a) := (hanti.mono fun _ hx => hx.1.le).injOn
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj
    (fun v => F v/sqrt ((v-σ)^2-v^3))
  rw [hmaps] at hchange
  have hjac (x : ℝ) (hx : x∈Ioo (0:ℝ) a) :
      |d x| *(F (f x)/sqrt ((f x-σ)^2-f x^3))=2*F (f x) := by
    have hpos : 0<f x := (hcore x).mpr (by rw [abs_of_pos hx.1]; exact hx.2)
    have hneg : d x<0 := (eulerState_peak m hm hs hμ hl he).2.2.2 x hx.1
    have hw := eulerState_first_integral m hμ l he x
    change d x^2=4*((f x-σ)^2-(max (f x) 0)^3) at hw
    rw [max_eq_left hpos.le] at hw
    have hP : 0<(f x-σ)^2-f x^3 := by nlinarith [sq_pos_of_neg hneg]
    have hsqrt := Real.sq_sqrt hP.le
    have hspos := sqrt_pos.mpr hP
    have hbranch : -d x=2*sqrt ((f x-σ)^2-f x^3) := by nlinarith
    rw [abs_of_neg hneg,hbranch]
    field_simp
  have hright : (∫ x in Ioo (0:ℝ) a,|d x| • (F (f x)/sqrt ((f x-σ)^2-f x^3)))=
      2*(∫ x in Ioo (0:ℝ) a,F (f x)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo fun x hx => by
      simpa only [smul_eq_mul] using hjac x hx
  rw [hright] at hchange
  have habs (x : ℝ) : f |x|=f x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx]
      exact (eulerState_even m hs μ l).1 x
  have hfull : (∫ x,F (f x))=2*(∫ x in Ioi (0:ℝ),F (f x)) := by
    have hh := integral_comp_abs (f := fun x => F (f x))
    simpa only [habs] using hh
  have hrestrict : (∫ x in Ioi (0:ℝ),F (f x))=∫ x in Ioo (0:ℝ) a,F (f x) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
    intro x hx
    apply hF
    by_contra! hpos
    have hxlt := (hcore x).mp hpos
    exact hx.2 ⟨hx.1,by rwa [abs_of_pos hx.1] at hxlt⟩
  rw [hfull,hrestrict]
  exact hchange.symm

end
end jacobi.Elliptic
