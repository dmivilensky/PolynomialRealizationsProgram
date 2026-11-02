import jacobi.Variational.SecondMoment

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
Translation acts on the actual density domain and preserves the literal mass,
energy, root mass and second spectral moment. These identities justify arbitrary
centers in the Young equality family and centering in variational arguments.
Source: translation invariance of Lebesgue measure, proved in mathlib.
Use: supplies all translated Young attainers without changing their constraints.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real
set_option backward.isDefEq.respectTransparency false

/-- Translation of an actual finite-energy density by an arbitrary center.
Use: supplies all translated Young attainers without changing their constraints.
Article: jacobi, Theorem D.5.
-/
def Density.translate (m : Density) (a : ℝ) : Density where
  value x := m.value (x-a)
  measurable := m.measurable.comp (measurable_id.sub measurable_const)
  nonneg x := m.nonneg (x-a)
  integrable := m.integrable.comp_sub_right a
  energy_integrable := m.energy_integrable.comp_sub_right a

/-- Translation preserves the actual total mass.
Use: a translated equality profile satisfies the same mass constraint.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: Lebesgue measure is invariant under x↦x-a. -/
theorem Density.translate_mass (m : Density) (a : ℝ) : (m.translate a).mass=m.mass :=
  integral_sub_right_eq_self m.value a

/-- Translation preserves the actual energy.
Use: every center of a Young profile attains the same optimal cost.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: translate the integrable 3/2-power energy integrand. -/
theorem Density.translate_energy (m : Density) (a : ℝ) : (m.translate a).energy=m.energy :=
  integral_sub_right_eq_self (fun x => m.value x^(3/2 : ℝ)) a

/-- Translation preserves the actual extended root mass, including infinity.
Use: centering does not weaken the root-mass constraint in Transfer.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: translate the nonnegative Lebesgue integrand directly. -/
theorem Density.translate_rootMass (m : Density) (a : ℝ) : (m.translate a).rootMass=m.rootMass :=
  lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (sqrt (m.value x))) a

/-- Translation preserves the genuine second spectral moment.
Use: all centers in the printed Young equality family have the same exact observation.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: identify the actual moment with its double kernel integral, translate each
integration variable, and use invariance of the distance x-y under a common translation. -/
theorem Density.translate_second (m : Density) (a : ℝ) :
    observe (m.translate a) .second=observe m .second := by
  -- Both changes of variables concern the literal kernel representation of the actual spectrum.
  rw [observe,L1Source.spectrum,chebyshev2.Continuum.kernelEigenvalue_square_integral]
  have hi (x : ℝ) : (∫ y, (m.translate a).value x*(m.translate a).value y*exp (-2*|x-y|)) =
      ∫ y, m.value (x-a)*m.value y*exp (-2*|(x-a)-y|) := by
    calc
      _ = ∫ y, m.value (x-a)*m.value (y-a)*exp (-2*|(x-a)-(y-a)|) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          dsimp only [Density.translate]
          rw [show (x-a)-(y-a)=x-y by ring]
      _ = _ := by
        simpa only using integral_sub_right_eq_self
          (fun y : ℝ => m.value (x-a)*m.value y*exp (-2*|(x-a)-y|)) a
  simp_rw [hi]
  calc
    _ = ∫ x, ∫ y, m.value x*m.value y*exp (-2*|x-y|) := by
      simpa only using integral_sub_right_eq_self
        (fun x : ℝ => ∫ y, m.value x*m.value y*exp (-2*|x-y|)) a
    _ = _ := (chebyshev2.Continuum.kernelEigenvalue_square_integral m.integrable m.nonneg).symm

end
end jacobi.Variational
