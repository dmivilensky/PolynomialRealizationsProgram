import polyak.Realization.ExplicitSpiral.PhasePowers

/-!
Article: analytic consequences of the three finite initialized-spiral sign lists.
Use: each certified sign controls a whole interval of times, including infinity.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section

/-- Article: a quadratic increasing from one is positive on the entire ray. -/
theorem quadratic_pos_of_derivative {a b c X : ℝ} (ha : 0<a)
    (h1 : 0<a+b+c) (hd : 0≤2*a+b) (hX : 1≤X) : 0<a*X^2+b*X+c := by
  have hs : 0≤a*(X-1)^2 := mul_nonneg ha.le (sq_nonneg _)
  have hp : 0≤(2*a+b)*(X-1) := mul_nonneg hd (by linarith)
  nlinarith

/-- Article: a negative discriminant proves positivity at every real time. -/
theorem quadratic_pos_of_discriminant {a b c X : ℝ} (ha : 0<a)
    (hd : 0<4*a*c-b^2) : 0<a*X^2+b*X+c := by
  have hh : 0<4*a*(a*X^2+b*X+c) := by nlinarith [sq_nonneg (2*a*X+b)]
  exact (mul_pos_iff_of_pos_left (by positivity : 0<4*a)).mp hh

/-- Article: the unit-disk norm certificate controls all decaying powers. -/
theorem disk_slack_pos {a c B X R : ℝ} (ha : 0≤a) (hB : 0≤B)
    (hc : 0<c) (hcB : 0<c^2-B^2) (_hX : 0≤X) (hX1 : X≤1)
    (hR : -B*X≤R) : 0<a*X^2+R+c := by
  have hb : B<c := by nlinarith
  have hbx : B*X≤B := by nlinarith
  nlinarith [mul_nonneg ha (sq_nonneg X)]

/-- Article: the large-growth three signs control the entire tail X≥X₀. -/
theorem tail_slack_pos {a c B X X0 R : ℝ} (ha : 0<a) (hB : 0≤B)
    (hX0 : 0≤X0) (hX : X0≤X) (hd : 0<4*a^2*X0^2-B^2)
    (hc : 0<a*X0^2+c) (hcB : 0<(a*X0^2+c)^2-B^2*X0^2)
    (hR : -B*X≤R) : 0<a*X^2+R+c := by
  have hder : 0<2*a*X0-B := by
    have hnon : 0≤2*a*X0 := by positivity
    nlinarith
  have hstart : 0<a*X0^2-B*X0+c := by
    have hnon : 0≤B*X0 := mul_nonneg hB hX0
    nlinarith
  have hsq : 0≤a*(X-X0)^2 := mul_nonneg ha.le (sq_nonneg _)
  have hincr : 0≤(2*a*X0-B)*(X-X0) := mul_nonneg hder.le (by linarith)
  nlinarith

/-- Article: every oscillatory real term has the phase-free lower bound. -/
theorem oscillation_lower (β Z : ℂ) : -‖β‖*‖Z‖≤(β*Z).re := by
  have hh := (abs_le.mp (Complex.abs_re_le_norm (β*Z))).1
  simpa only [norm_mul,neg_mul] using hh

/-- Article: the residue approximation loses at most |β| times its phase error. -/
theorem residue_oscillation_lower {β E E0 : ℂ} {D X : ℝ}
    (hβ : ‖β‖≤1) (hX : 0≤X) (_hD : 0≤D) (hE : ‖E-E0‖≤D) :
    X*(β*E0).re-X*D≤X*(β*E).re := by
  have he : β*E=β*E0+β*(E-E0) := by ring
  have hb := oscillation_lower β (E-E0)
  have hbd : ‖β‖*‖E-E0‖≤D := by
    calc
      _ ≤ 1*D := mul_le_mul hβ hE (norm_nonneg _) (by norm_num)
      _ = D := one_mul D
  rw [he,Complex.add_re]
  nlinarith

end
end polyak.Realization.ExplicitSpiral
