import polyak.Levels.Geometry.Cotangent
import polyak.Levels.Chart.Coefficients

/-! The generic differential identities specialized to the article's
actual tuning, including zero momentum. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set Filter
open scoped Topology

def cotangent (q : Tuning) (ω : ℝ) : ℝ := q.Xi (Real.cos ω)/Real.sin ω

theorem cotangent_eq_poly (q : Tuning) : cotangent q=
    polyCotangent (Chart.coefficients q).c0 (Chart.coefficients q).c1 (Chart.coefficients q).c2 := by
  funext ω
  rw [cotangent,←Chart.eval_coefficients]
  rfl

def cotangentFirst (q : Tuning) : ℝ→ℝ :=
  polyCotangentFirst (Chart.coefficients q).c0 (Chart.coefficients q).c1 (Chart.coefficients q).c2

def cotangentSecond (q : Tuning) : ℝ→ℝ :=
  polyCotangentSecond (Chart.coefficients q).c0 (Chart.coefficients q).c1 (Chart.coefficients q).c2

theorem hasDerivAt_cotangent (q : Tuning) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi) :
    HasDerivAt (cotangent q) (cotangentFirst q ω) ω := by
  rw [cotangent_eq_poly]
  exact hasDerivAt_polyCotangent _ _ _ (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2).ne'

theorem hasDerivAt_cotangentFirst (q : Tuning) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi) :
    HasDerivAt (cotangentFirst q) (cotangentSecond q ω) ω :=
  hasDerivAt_polyCotangentFirst _ _ _ (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2).ne'

theorem deriv_cotangent (q : Tuning) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi) :
    deriv (cotangent q) ω=cotangentFirst q ω := (hasDerivAt_cotangent q hω).deriv

theorem deriv2_cotangent (q : Tuning) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi) :
    deriv^[2] (cotangent q) ω=cotangentSecond q ω := by
  have he : deriv (cotangent q)=ᶠ[𝓝 ω] cotangentFirst q := by
    filter_upwards [isOpen_Ioo.mem_nhds hω] with x hx
    exact deriv_cotangent q hx
  change deriv (deriv (cotangent q)) ω=_
  rw [he.deriv_eq]
  exact (hasDerivAt_cotangentFirst q hω).deriv

theorem cotangentSecond_neg (q : Tuning) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi) :
    cotangentSecond q ω<0 := by
  have hp:=q.Xi_one_neg
  have hm:=q.Xi_neg_one_neg
  rw [←Chart.eval_coefficients] at hp hm
  simp only [Chart.Coefficients.eval,one_pow,mul_one,neg_one_sq,mul_neg_one] at hp hm
  have hc : (Chart.coefficients q).c2≤0 := by
    dsimp [Chart.coefficients]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [q.beta_nonneg])
      (by positivity [q.B_pos,q.beta_lt_one])
  exact polyCotangentSecond_neg hp (by linarith) hc hω

/-- The exact strict concavity assertion of Theorem convex. -/
theorem cotangent_strictConcaveOn (q : Tuning) :
    StrictConcaveOn ℝ (Ioo 0 Real.pi) (cotangent q) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ioo 0 Real.pi)
  · intro ω hω
    exact (hasDerivAt_cotangent q hω).continuousAt.continuousWithinAt
  · intro ω hω
    rw [interior_Ioo] at hω
    rw [deriv2_cotangent q hω]
    exact cotangentSecond_neg q hω

/-- Literal endpoint-weighted identity in Theorem convex. -/
theorem cotangentSecond_endpoint_identity (q : Tuning) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi) :
    deriv^[2] (cotangent q) ω*(Real.sin ω)^3=
      (1/2:ℝ)*(1+Real.cos ω)^2*q.Xi 1+
      (1/2:ℝ)*(1-Real.cos ω)^2*q.Xi (-1)+
      (Chart.coefficients q).c2*(1-(Real.cos ω)^2)^2 := by
  rw [deriv2_cotangent q hω,←Chart.eval_coefficients q 1,←Chart.eval_coefficients q (-1)]
  simpa only [cotangentSecond,Chart.Coefficients.eval,one_pow,mul_one,neg_one_sq,mul_neg_one,
    sub_eq_add_neg] using
    polyCotangentSecond_endpoint_identity (Chart.coefficients q).c0 (Chart.coefficients q).c1
      (Chart.coefficients q).c2 ω (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2).ne'

end polyak.Levels.Geometry
