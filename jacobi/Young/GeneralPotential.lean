import jacobi.Young.H1Scaling

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
Riesz representation on the existing exact H1 space constructs the genuine
Green potential without assuming finite mass. Its actual integral kernel,
Sobolev regularity and Green energy identity are proved. These allow the
same sharp inequality and equality argument for every finite-energy source.
Source: Holder, Riesz representation and exact changes of spatial scale.
Use: matches the scope of the article's global sharp Young theorem and its equality cases.
-/
namespace jacobi.Young
noncomputable section
open Real MeasureTheory Filter chebyshev2.Sobolev
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The full nonnegative finite-energy source domain, with no finite-mass restriction.
Use: matches the scope of the article's global sharp Young theorem and its equality cases.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
structure EnergySource where
  /-- The actual source function. -/
  value : ℝ → ℝ
  /-- Measurability of the actual source, required by all product integrals. -/
  measurable : Measurable value
  /-- Pointwise nonnegativity fixes every real-power branch. -/
  nonneg : ∀ x, 0≤value x
  /-- The only global integrability hypothesis of the printed theorem. -/
  energy_integrable : Integrable (fun x => value x^(3/2 : ℝ))

namespace EnergySource

/-- The literal energy integral on the full source domain.
Use: the exact objective in the unrestricted sharp Young theorem.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def energy (m : EnergySource) : ℝ := ∫ x, m.value x^(3/2 : ℝ)

/-- Rescaling converts the exponent-one Sobolev Green kernel to exponent two.
Use: reuses the existing H1 space and its reproducing features without rebuilding a Hilbert space.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def rescaled (m : EnergySource) : EnergySource where
  value x := m.value (x/2)
  measurable := m.measurable.comp (measurable_id.div_const 2)
  nonneg x := m.nonneg _
  energy_integrable := by
    simpa only [div_eq_inv_mul] using (integrable_comp_mul_left_iff
      (fun x => m.value x^(3/2 : ℝ)) (by norm_num : (2:ℝ)⁻¹≠0)).mpr m.energy_integrable

/-- The actual exponent-one Green solution supplied by Hilbert-space Riesz representation.
Use: constructs a genuine Sobolev potential even for a source of infinite total mass.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def weakConvolution (m : EnergySource) : H1 := (InnerProductSpace.toDual ℝ H1).symm
  ((2 : ℝ) • energyDual m.measurable m.nonneg m.energy_integrable)

/-- The constructed Green element has the exact weak source pairing.
Use: proves its kernel representation and exact energy identity without unproved existence premises.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: apply the inverse Riesz isometry and its defining inner-product identity. -/
theorem weakConvolution_form (m : EnergySource) (v : H1) :
    inner ℝ v m.weakConvolution=2*(∫ x, m.value x*H1.rep v x) := by
  rw [real_inner_comm,weakConvolution,InnerProductSpace.toDual_symm_apply]
  change 2*(energyDual m.measurable m.nonneg m.energy_integrable) v=_
  simp only [energyDual,LinearMap.mkContinuous_apply]
  rfl

/-- The literal exponentially weighted source is integrable at every center.
Use: kernel values and their product-space interpretation are genuine integrals even for infinite mass.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: the exponent-one kernel is twice the Sobolev reproducing representative,
whose product with the source is integrable by the proved Holder pairing. -/
theorem weakConvolution_integrand_integrable (m : EnergySource) (x : ℝ) :
    Integrable (fun y => m.value y*exp (-|x-y|)) := by
  -- The reproducing function belongs to the existing H1 space at every center.
  apply ((energy_pair_integrable m.measurable m.nonneg m.energy_integrable (H1.k x)).const_mul 2).congr
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [H1.k_rep,abs_sub_comm x y]
    ring

/-- The Riesz solution equals the literal exponential Green convolution at every point.
Use: positivity and the true double-integral second moment remain tied to the original source.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: test the exact weak pairing against the existing Sobolev reproducing vector. -/
theorem weakConvolution_kernel (m : EnergySource) (x : ℝ) :
    H1.rep m.weakConvolution x=∫ y, m.value y*exp (-|x-y|) := by
  rw [← H1.reproducing,weakConvolution_form,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [H1.k_rep,abs_sub_comm x y]
    ring

/-- The actual exponent-two potential for any nonnegative finite-energy source.
Use: the sharp Sobolev and Holder chain is applied in exactly the article's normalization.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def green (m : EnergySource) (x : ℝ) : ℝ := (1/2 : ℝ)*H1.rep m.rescaled.weakConvolution (2*x)

/-- A genuine weak derivative of the full-domain Green potential.
Use: states its actual Sobolev membership and exact quadratic energy.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def greenSlope (m : EnergySource) (x : ℝ) : ℝ := H1.slope m.rescaled.weakConvolution (2*x)

/-- The full-domain Green potential is an actual locally absolutely continuous H1 representative.
Use: the sharp Sobolev theorem applies with no L1 premise on the original source.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: apply the proved Sobolev scaling theorem to the actual Riesz element. -/
theorem green_sobolev (m : EnergySource) : SobolevRegular m.green m.greenSlope := by
  convert sobolev_scale (H1.regular m.rescaled.weakConvolution) (by norm_num : (2:ℝ)≠0) (1/2 : ℝ) using 1
  · funext x; dsimp only [green]
  · funext x; dsimp only [greenSlope]; ring

/-- The full-domain Green potential equals the actual article kernel integral.
Use: identifies every quantity in the unrestricted sharp Young equality chain.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: substitute z=2y in the proved exponent-one Riesz kernel formula and cancel its Jacobian. -/
theorem green_kernel (m : EnergySource) (x : ℝ) :
    m.green x=∫ y, m.value y*exp (-2*|x-y|) := by
  -- Riesz gives existence before any change of variables is made.
  rw [green,weakConvolution_kernel]
  have h := Measure.integral_comp_mul_left
    (fun z : ℝ => m.rescaled.value z*exp (-|2*x-z|)) (2 : ℝ)
  norm_num only [invOf_eq_inv,inv_eq_one_div,abs_of_pos (by norm_num : (0:ℝ)<2⁻¹),smul_eq_mul] at h
  rw [← h]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only [rescaled]
    rw [show (2*y)/2=y by ring,show 2*x-2*y=2*(x-y) by ring,
      abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    congr 2
    ring

/-- Every actual full-domain potential is nonnegative.
Use: the sharp nonnegative Sobolev theorem applies without sign assumptions on an abstract weak solution.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: integrate the nonnegative literal kernel integrand. -/
theorem green_nonneg (m : EnergySource) (x : ℝ) : 0≤m.green x := by
  rw [green_kernel]
  exact integral_nonneg (fun y => mul_nonneg (m.nonneg y) (exp_pos _).le)

/-- The actual density-potential pairing is integrable in the full source domain.
Use: the second moment and Green energy are finite genuine integrals.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: the scaled potential is a true H1 representative; Holder pairing with the source is integrable. -/
theorem green_pair_integrable (m : EnergySource) : Integrable (fun x => m.value x*m.green x) := by
  obtain ⟨u,hu⟩ := (H1.range_iff m.green).mpr ⟨m.greenSlope,m.green_sobolev⟩
  simpa only [hu] using energy_pair_integrable m.measurable m.nonneg m.energy_integrable u

/-- The full-domain potential has an integrable cube.
Use: the unrestricted Holder/Sobolev equality chain uses an actual finite cubic moment.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: apply the established cubic H1 bound to its actual representative and remove nonnegative absolute values. -/
theorem green_cube_integrable (m : EnergySource) : Integrable (fun x => m.green x^3) := by
  obtain ⟨u,hu⟩ := (H1.range_iff m.green).mpr ⟨m.greenSlope,m.green_sobolev⟩
  have h := (h1_absolute_cube u).1
  simpa only [hu,abs_of_nonneg (m.green_nonneg _)] using h

/-- The exact Green energy identity on the full, possibly infinite-mass source domain.
Use: closes the sharp Sobolev/Holder chain without an unproved finite-mass approximation assumption.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: test the exact Riesz form against its own solution and rescale its
derivative, value and source integrals by z=2x with their exact Jacobians. -/
theorem green_energy (m : EnergySource) :
    (∫ x, m.greenSlope x^2)+4*(∫ x, m.green x^2)=4*(∫ x, m.value x*m.green x) := by
  -- The weak Riesz energy and every term below concern the same actual potential.
  let U := m.rescaled.weakConvolution
  have he := m.rescaled.weakConvolution_form U
  rw [real_inner_self_eq_norm_sq,H1.norm_sq_energy] at he
  have hd : (∫ x, m.greenSlope x^2)=(1/2 : ℝ)*(∫ x, H1.slope U x^2) := by
    simpa only [greenSlope,smul_eq_mul,invOf_eq_inv,inv_eq_one_div,
      abs_of_pos (by norm_num : (0:ℝ)<1/2)] using
      Measure.integral_comp_mul_left (fun x => H1.slope U x^2) 2
  have hv : (∫ x, m.green x^2)=(1/8 : ℝ)*(∫ x, H1.rep U x^2) := by
    simp_rw [green,mul_pow]
    rw [integral_const_mul,Measure.integral_comp_mul_left (fun x => H1.rep U x^2)]
    norm_num [smul_eq_mul]
    ring
  have hp : (∫ x, m.rescaled.value x*H1.rep U x)=4*(∫ x, m.value x*m.green x) := by
    have h := Measure.integral_comp_mul_left (fun x => m.rescaled.value x*H1.rep U x) (2 : ℝ)
    have hs : (fun x => m.rescaled.value (2*x)*H1.rep U (2*x))=
        (fun x => 2*(m.value x*m.green x)) := by
      funext x
      dsimp [rescaled,green,U]
      rw [show (2*x)/2=x by ring]
      ring
    rw [hs,integral_const_mul] at h
    norm_num [smul_eq_mul] at h
    linarith
  rw [hd,hv]
  linarith

end EnergySource
end
end jacobi.Young
