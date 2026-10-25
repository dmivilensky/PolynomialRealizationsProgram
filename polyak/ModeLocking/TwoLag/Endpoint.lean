import polyak.ModeLocking.TwoLag.Factor
import polyak.Levels.Geometry.LagEnds

/-! Exact endpoint curvature criterion, including the removable value of Psi. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels

def endpointMoment (q : Tuning) (K : ℕ) (a b : ℝ) : ℝ :=
  a*(1+2*Geometry.tau q)+b*(K : ℝ)*((K : ℝ)-2*Geometry.tau q)

theorem endpointMoment_factor (q : Tuning) {K : ℕ} (hK : 1≤K)
    {a b : ℝ} (ha : 0<a) (hb : 0≤b) :
    endpointMoment q K a b =
      (-a/q.Xi 1)*(1+(b/a)*(K : ℝ)^2)*(Psi K (b/a) 1-q.Xi 1) := by
  have hd : 1+(b/a)*(K : ℝ)^2 ≠ 0 := by positivity
  have hd' : a+b*(K : ℝ)^2 ≠ 0 := by positivity
  rw [Psi_one hK]
  dsimp [endpointMoment, Geometry.tau]
  field_simp [ha.ne', q.Xi_one_neg.ne, hd, hd']
  ring

theorem endpointMoment_pos_iff (q : Tuning) {K : ℕ} (hK : 1≤K)
    {a b : ℝ} (ha : 0<a) (hb : 0≤b) :
    0<endpointMoment q K a b ↔ q.Xi 1<Psi K (b/a) 1 := by
  rw [endpointMoment_factor q hK ha hb]
  have hp : 0<(-a/q.Xi 1)*(1+(b/a)*(K : ℝ)^2) := by
    apply mul_pos (div_pos_of_neg_of_neg (neg_neg_of_pos ha) q.Xi_one_neg)
    positivity
  constructor
  · intro h
    exact sub_pos.mp (pos_of_mul_pos_right h hp.le)
  · intro h
    exact mul_pos hp (sub_pos.mpr h)

end polyak.ModeLocking.TwoLag
