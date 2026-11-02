import jacobi.Young.GeneralPotential

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
The actual Green pairing equals the extended nonnegative double integral
printed in the article. Both are finite for every finite-energy source.
Strict positivity for a nonzero source is proved directly from the positive
kernel, with no assumed finite total mass or spectral decomposition.
Source: Tonelli, Holder and strict positivity of the exponential kernel.
Use: identifies the full-domain double integral with the actual Green pairing.
-/
namespace jacobi.Young.EnergySource
noncomputable section
open Real MeasureTheory Filter
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Every exponent-two convolution integrand is genuinely integrable at each center.
Use: identifies the full-domain double integral with the actual Green pairing.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: rescale the previously proved integrable exponent-one reproducing-kernel pairing. -/
theorem green_integrand_integrable (m : EnergySource) (x : ℝ) :
    Integrable (fun y => m.value y*exp (-2*|x-y|)) := by
  -- The factor two rescales a finite integral, even though the unweighted source may have infinite mass.
  apply ((m.rescaled.weakConvolution_integrand_integrable (2*x)).comp_mul_left'
    (by norm_num : (2:ℝ)≠0)).congr
  exact Eventually.of_forall fun y => by
    dsimp only [rescaled]
    rw [show (2*y)/2=y by ring,show 2*x-2*y=2*(x-y) by ring,
      abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    congr 2
    ring

/-- The actual nonnegative second-moment pairing on the full finite-energy source domain.
Use: the sharp inequality and all its equality arguments use a finite real moment before returning to the printed double integral.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def second (m : EnergySource) : ℝ := ∫ x, m.value x*m.green x

/-- The Green pairing is the article's genuine nonnegative product-space second moment.
Use: equality classification on the full domain concerns the literal printed integral, not a substitute functional.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: Tonelli separates the nonnegative double integral. The proved pointwise
absolute convergence identifies each inner integral with u(x); integrability
of the actual source-potential pairing returns its finite real integral. -/
theorem second_lintegral (m : EnergySource) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (m.value z.1*m.value z.2*exp (-2*|z.1-z.2|)) ∂volume.prod volume)=
      ENNReal.ofReal m.second := by
  -- Tonelli precedes every real double-integral operation, so infinite-mass junk values cannot occur.
  have hm : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal
      (m.value z.1*m.value z.2*exp (-2*|z.1-z.2|))) :=
    ENNReal.continuous_ofReal.measurable.comp
      (((m.measurable.comp measurable_fst).mul (m.measurable.comp measurable_snd)).mul
        (by fun_prop : Measurable (fun z : ℝ × ℝ => exp (-2*|z.1-z.2|))))
  rw [lintegral_prod _ hm.aemeasurable]
  have hp (x : ℝ) : (∫⁻ y, ENNReal.ofReal (m.value x*m.value y*exp (-2*|x-y|)))=
      ENNReal.ofReal (m.value x*m.green x) := by
    have hi : Integrable (fun y => m.value x*m.value y*exp (-2*|x-y|)) :=
      ((m.green_integrand_integrable x).const_mul (m.value x)).congr
        (Eventually.of_forall fun _ => by dsimp only; ring)
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun y =>
      mul_nonneg (mul_nonneg (m.nonneg x) (m.nonneg y)) (exp_pos _).le),green_kernel,
      ← integral_const_mul]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => by dsimp only; ring
  simp_rw [hp]
  exact (ofReal_integral_eq_lintegral_ofReal m.green_pair_integrable
    (Eventually.of_forall fun x => mul_nonneg (m.nonneg x) (m.green_nonneg x))).symm

/-- Every positive kernel pairing with a nonzero finite-energy source is strictly positive.
Use: verifies nonzero potential and nonzero second moment in the full-domain equality argument.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: if its nonnegative integrable product had zero integral, the strictly
positive kernel would force the source to vanish almost everywhere and its energy to be zero. -/
theorem positive_pair (m : EnergySource) (hE : 0<m.energy) {k : ℝ → ℝ}
    (hk : ∀ x, 0<k x) (hi : Integrable (fun x => m.value x*k x)) :
    0<(∫ x, m.value x*k x) := by
  -- This argument never uses integrability of the unweighted source.
  apply lt_of_le_of_ne (integral_nonneg (fun x => mul_nonneg (m.nonneg x) (hk x).le))
  intro hz
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (m.nonneg x) (hk x).le) hi).mp hz.symm
  have he0 : m.energy=0 := by
    change (∫ x, m.value x^(3/2 : ℝ))=0
    have hm0 : (fun x => m.value x^(3/2 : ℝ))=ᵐ[volume] (0 : ℝ → ℝ) := by
      filter_upwards [hae] with x hx
      have hmx : m.value x=0 := (mul_eq_zero.mp hx).resolve_right (hk x).ne'
      simp only [hmx,Real.zero_rpow (by norm_num : (3/2 : ℝ)≠0),Pi.zero_apply]
    simpa only [Pi.zero_apply,integral_zero] using integral_congr_ae hm0
  exact hE.ne' he0

/-- Every nonzero finite-energy source has a strictly positive actual potential at every point.
Use: excludes zero denominators and zero moments when classifying unrestricted equality.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: its literal exponential kernel is strictly positive and its actual source pairing is integrable. -/
theorem green_pos (m : EnergySource) (hE : 0<m.energy) (x : ℝ) : 0<m.green x := by
  rw [green_kernel]
  exact positive_pair m hE (fun y => exp_pos _) (m.green_integrand_integrable x)

/-- Every nonzero finite-energy source has a strictly positive actual second moment.
Use: the coefficient E/G in the full-domain Holder rigidity argument is well defined.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: the actual potential is strictly positive and the proved Green pairing is integrable. -/
theorem second_pos (m : EnergySource) (hE : 0<m.energy) : 0<m.second :=
  positive_pair m hE (m.green_pos hE) m.green_pair_integrable

end
end jacobi.Young.EnergySource
