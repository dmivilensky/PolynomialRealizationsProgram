import jacobi.Variational.EnergyVariation

/-!
Article: jacobi, Lemma D.3.
Nonnegative sums and convex segments stay in the actual L1 intersect
L^(3/2) density domain. Mass and every integrable linear test have their
exact segment formulas. The objective linear test is proved integrable
for all competitors, preparing the finite-dimensional separation argument.
Source: elementary real-power bounds and linearity of the Lebesgue integral.
Use: the variational domain is a genuine convex cone, including unbounded measurable densities.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set
set_option backward.isDefEq.respectTransparency false

/-- The 3/2 energy of a sum is bounded by an integrable multiple of the separate energies.
Use: the variational domain is a genuine convex cone, including unbounded measurable densities.
Article: jacobi, Lemma D.3.
Proof: bound sqrt(a+b) by sqrt(a)+sqrt(b), then control both mixed products by the separate energies. -/
theorem energy_sum_bound {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    (a+b)^(3/2:ℝ)≤3*(a^(3/2:ℝ)+b^(3/2:ℝ)) := by
  -- The coarse constant three is used only for domain closure, not for any sharp estimate.
  have hs : sqrt (a+b)≤sqrt a+sqrt b := by
    nlinarith [Real.sq_sqrt (add_nonneg ha hb),Real.sq_sqrt ha,Real.sq_sqrt hb,
      sqrt_nonneg (a+b),sqrt_nonneg a,sqrt_nonneg b,mul_nonneg (sqrt_nonneg a) (sqrt_nonneg b)]
  have hp := mul_le_mul_of_nonneg_left hs (add_nonneg ha hb)
  have h1 := sqrt_product_energy_bound ha hb
  have h2 := sqrt_product_energy_bound hb ha
  rw [rpow_three_halves (add_nonneg ha hb),rpow_three_halves ha,rpow_three_halves hb] at *
  nlinarith

/-- Addition in the actual nonnegative finite-energy density cone.
Use: constructs convex variations inside the exact article domain.
Article: jacobi, Lemma D.3.
-/
def Density.add (m q : Density) : Density where
  value x := m.value x+q.value x
  measurable := m.measurable.add q.measurable
  nonneg x := add_nonneg (m.nonneg x) (q.nonneg x)
  integrable := m.integrable.add q.integrable
  energy_integrable := by
    apply ((m.energy_integrable.add q.energy_integrable).const_mul 3).mono'
    · exact ((m.measurable.add q.measurable).pow_const (3/2:ℝ)).aestronglyMeasurable
    · exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (add_nonneg (m.nonneg x) (q.nonneg x)) _)]
        exact energy_sum_bound (m.nonneg x) (q.nonneg x)

/-- The literal convex segment between any two finite-energy densities.
Use: every cone direction q-m is realized by an actual admissible one-sided path.
Article: jacobi, Lemma D.3.
-/
def Density.segment (m q : Density) (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) : Density :=
  (m.scale (1-t) (sub_nonneg.mpr ht1)).add (q.scale t ht0)

/-- The actual convex segment has exactly the affine pointwise formula used in the variations.
Use: identifies its energy and spectral remainders with the previously proved directional formulas.
Article: jacobi, Lemma D.3.
Proof: expand the two nonnegative amplitude scalings and collect coefficients. -/
theorem Density.segment_value (m q : Density) (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) (x : ℝ) :
    (m.segment q t ht0 ht1).value x=m.value x+t*(q.value x-m.value x) := by
  change (1-t)*m.value x+t*q.value x=_
  ring

/-- The mass of the actual segment is affine, including at both endpoints.
Use: a nonpositive mass direction preserves an active mass constraint exactly.
Article: jacobi, Lemma D.3.
Proof: integrate the two actual scaled summands and collect their mass coefficients. -/
theorem Density.segment_mass (m q : Density) (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    (m.segment q t ht0 ht1).mass=m.mass+t*(q.mass-m.mass) := by
  change (∫ x,(1-t)*m.value x+t*q.value x)=_
  rw [integral_add (m.integrable.const_mul _) (q.integrable.const_mul _),integral_const_mul,integral_const_mul]
  change (1-t)*m.mass+t*q.mass=_
  ring

/-- Every objective linear test is integrable on every finite-energy competitor.
Use: supplies the finite objective coordinate for separation of the variation cone.
Article: jacobi, Lemma D.3.
Proof: bound the nonnegative product by the sum of the two finite energy integrands. -/
theorem objectivePair_integrable (m q : Density) : Integrable (fun x => sqrt (m.value x)*q.value x) := by
  apply (m.energy_integrable.add q.energy_integrable).mono'
  · exact (m.measurable.sqrt.mul q.measurable).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sqrt_nonneg _) (q.nonneg x))]
      exact sqrt_product_energy_bound (m.nonneg x) (q.nonneg x)

/-- The objective's linear functional on the full admissible density cone.
Use: one of the three real coordinates in the finite-dimensional multiplier separation.
Article: jacobi, Lemma D.3.
-/
def objectivePair (m q : Density) : ℝ := (3/2:ℝ)*(∫ x,sqrt (m.value x)*q.value x)

/-- The objective coordinate of a density difference is its actual first derivative.
Use: converts the finite-dimensional separation coordinate to the energy path derivative.
Article: jacobi, Lemma D.3.
Proof: both objective pairings are integrable, so their difference can be placed under the integral. -/
theorem objectivePair_sub (m q : Density) :
    objectivePair m q-objectivePair m m=(3/2:ℝ)*(∫ x,sqrt (m.value x)*(q.value x-m.value x)) := by
  unfold objectivePair
  rw [← mul_sub,← integral_sub (objectivePair_integrable m q) (objectivePair_integrable m m)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by dsimp only; ring

/-- The actual L1 size of a nonnegative segment increment is exactly linear in its parameter.
Use: the quadratic spectral remainder becomes a genuine O(t²) error along every admissible direction.
Article: jacobi, Lemma D.3.
Proof: the affine segment formula factors t, whose nonnegativity removes its absolute value. -/
theorem Density.segment_l1 (m q : Density) (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    (∫ x,|(m.segment q t ht0 ht1).value x-m.value x|)=t*(∫ x,|q.value x-m.value x|) := by
  simp_rw [m.segment_value q t ht0 ht1,add_sub_cancel_left,abs_mul,abs_of_nonneg ht0]
  exact integral_const_mul t _

/-- Any integrable linear density test has its exact convex-segment formula.
Use: proves convexity of the finite-dimensional variation image for Hahn--Banach separation.
Article: jacobi, Lemma D.3.
Proof: distribute the two segment coefficients, then use the integrable linearity of the Lebesgue integral. -/
theorem densityTest_segment (g : ℝ → ℝ) (m q : Density)
    (hm : Integrable (fun x => g x*m.value x)) (hq : Integrable (fun x => g x*q.value x))
    (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    (∫ x,g x*(m.segment q t ht0 ht1).value x)=
      (1-t)*(∫ x,g x*m.value x)+t*(∫ x,g x*q.value x) := by
  -- Integrability of the two separate tests is available before distributing the integral.
  have he : (fun x => g x*(m.segment q t ht0 ht1).value x)=
      (fun x => (1-t)*(g x*m.value x))+(fun x => t*(g x*q.value x)) := by
    funext x
    change g x*((1-t)*m.value x+t*q.value x)=_
    simp only [Pi.add_apply]
    ring
  rw [he,integral_add' (hm.const_mul _) (hq.const_mul _),integral_const_mul,integral_const_mul]

end
end jacobi.Variational
