import jacobi.Variational.GreenSpatialDerivative

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
One fixed strictly subcritical upper coupling dominates every positive
parameter derivative on its closed interval. The actual upper Green-ratio
source is product-integrable by its proved exact vertical integral. This
supplies a single integrable majorant for the full spatial determinant
family and discharges dominated differentiation on the infinite line.
Source: actual kernel monotonicity, diagonal bounds and the Green-ratio integral.
Use: bounds the spatial determinant derivative by a single upper endpoint kernel.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Squared actual Green ratios at every smaller nonnegative coupling obey one fixed spectral-margin comparison.
Use: bounds the spatial determinant derivative by a single upper endpoint kernel.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: kernel monotonicity and g_t>=1/2 give G_t/g_t<=2G_b.
The upper endpoint bound 2g_b<=C then gives 2G_b<=C*G_b/g_b.
All entries and denominators are positive, so squaring preserves the inequality. -/
theorem L1Source.greenParameter_ratio_bound (m : L1Source) {t b : ℝ} (ht : 0≤t) (htb : t≤b)
    (hp : b*observe m .top<1) (x y : ℝ) :
    (m.greenParameter t x y/m.greenParameter t x x)^2≤
      ((1-b*observe m .top)⁻¹)^2*(m.greenParameter b x y/m.greenParameter b x x)^2 := by
  -- The original upper pole margin controls both actual inverses in the comparison.
  have htop := (chebyshev2.Continuum.kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg 0
  have hpt : t*observe m .top<1 := (mul_le_mul_of_nonneg_right htb htop).trans_lt hp
  have hb : 0≤b := ht.trans htb
  let A := m.fredholmGreen t ht hpt
  let B := m.fredholmGreen b hb hp
  let C := (1-b*observe m .top)⁻¹
  have hA : 0<A x x := m.fredholmGreen_pos ht hpt x x
  have hB : 0<B x x := m.fredholmGreen_pos hb hp x x
  have hBy : 0<B x y := m.fredholmGreen_pos hb hp x y
  have hAy : 0<A x y := m.fredholmGreen_pos ht hpt x y
  have hmono : A x y≤B x y := m.fredholmGreen_mono_parameter ht htb hp x y
  have hlow : (1/2:ℝ)≤A x x := (m.fredholmGreen_diagonal ht hpt x).1
  have hupp : 2*B x x≤C := by
    have hh := mul_le_mul_of_nonneg_left (m.fredholmGreen_diagonal hb hp x).2 (by norm_num : (0:ℝ)≤2)
    convert hh using 1
    dsimp only [C]
    field_simp
  have h₁ : A x y/A x x≤2*B x y := by
    apply (div_le_iff₀ hA).mpr
    have hh := mul_le_mul_of_nonneg_left hlow
      (by positivity : 0≤2*B x y)
    nlinarith
  have h₂ : 2*B x y≤C*(B x y/B x x) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hB).mpr
    have hh := mul_le_mul_of_nonneg_right hupp hBy.le
    nlinarith
  have hsq := pow_le_pow_left₀ (div_nonneg hAy.le hA.le) (h₁.trans h₂) 2
  simp only [mul_pow] at hsq
  simpa only [m.greenParameter_eq ht hpt,m.greenParameter_eq hb hp,A,B,C] using hsq

/-- The fixed actual upper-coupling majorant for all spatial regularized determinant derivatives.
Use: proves convergence and dominated differentiation of the entire spatial integral family on [0,b].
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def L1Source.greenSpatialMajorant (m : L1Source) (b : ℝ) (hb : 0≤b) (hp : b*observe m .top<1)
    (x : ℝ) : ℝ := ((1-b*observe m .top)⁻¹)^2*(∫ y,m.greenRatioSource b hb hp (x,y))+m.value x

/-- The actual spatial majorant is genuinely integrable on the full line.
Use: supplies the common majorant required by both dominated convergence and dominated differentiation.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the upper Green-ratio source is product-integrable, so its horizontal
integral is integrable; scaling and adding the original L1 density preserve integrability. -/
theorem L1Source.greenSpatialMajorant_integrable (m : L1Source) (hc : Continuous m.value) {b : ℝ}
    (hb : 0≤b) (hp : b*observe m .top<1) : Integrable (m.greenSpatialMajorant b hb hp) :=
  ((m.greenRatioSource_integrable hc hb hp).integral_prod_left.const_mul _).add m.integrable

/-- One fixed actual integrable majorant bounds all spatial determinant derivatives on a closed subcritical coupling interval.
Use: discharges the final analytic domination premise without a user-supplied convergence or numerical certificate.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the positive Green-ratio comparison bounds the derivative's source
integral by C² times the upper endpoint source. Fubini gives integrable
upper horizontal slices on one common full-measure set, independent of the varying coupling. -/
theorem L1Source.greenSpatialDerivative_bound (m : L1Source) (hc : Continuous m.value) {b : ℝ}
    (hb : 0≤b) (hp : b*observe m .top<1) :
    ∀ᵐ x : ℝ,∀ t∈Icc (0:ℝ) b,‖m.greenSpatialDerivative t x‖≤m.greenSpatialMajorant b hb hp x := by
  -- The full-measure set depends only on the fixed dominating upper kernel.
  filter_upwards [(m.greenRatioSource_integrable hc hb hp).prod_right_ae] with x hx
  intro t ht
  let C := (1-b*observe m .top)⁻¹
  let H (y : ℝ) := m.value y*(m.greenParameter t x y/m.greenParameter t x x)^2
  have hmono : (∫ y,H y)≤C^2*(∫ y,m.greenRatioSource b hb hp (x,y)) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun y => mul_nonneg (m.nonneg y) (sq_nonneg _)) (hx.const_mul (C^2))
    exact Eventually.of_forall fun y => by
      have hh := mul_le_mul_of_nonneg_left (m.greenParameter_ratio_bound ht.1 ht.2 hp x y) (m.nonneg y)
      dsimp only [H,C,L1Source.greenRatioSource,L1Source.greenDiagonal]
      rw [← m.greenParameter_eq hb hp x y,← m.greenParameter_eq hb hp x x]
      nlinarith
  have hnon : 0≤∫ y,H y := integral_nonneg fun y => mul_nonneg (m.nonneg y) (sq_nonneg _)
  change ‖(∫ y,H y)-m.value x‖≤C^2*(∫ y,m.greenRatioSource b hb hp (x,y))+m.value x
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |∫ y,H y|+|m.value x| := abs_sub _ _
    _ = (∫ y,H y)+m.value x := by rw [abs_of_nonneg hnon,abs_of_nonneg (m.nonneg x)]
    _ ≤ _ := add_le_add hmono le_rfl

end
end jacobi.Variational
