import polyak.FareyPlateau.FanAnalysis.FiniteTests

/-! The explicit positive quadratic coefficients at the two neighbors of the
origin, retained separately for compact-uniform estimates. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.Actual
open General Levels ModeLocking Filter
open scoped Topology
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem zero_neighbor_limits (e : ℝ) :
    Tendsto (fun δ => phi A e δ ((k : ℝ)*δ)/δ^2) (𝓝[≠] 0)
      (𝓝 (4*u A*(k : ℝ)^2*(1-A.mix))) ∧
    Tendsto (fun δ => phi A e δ (-(k : ℝ)*δ)/δ^2) (𝓝[≠] 0)
      (𝓝 (4*u A*(k : ℝ)^2*A.mix)) := by
  have hplus := near_zero_limit A e (correction A) (k : ℝ)
  have hminus := near_zero_limit A e (correction A) (-(k : ℝ))
  have heplus : u A*((k : ℝ)^2-2*first A*k)-v A*correction A*k=
      2*u A*(k : ℝ)^2*(1-A.mix) := by
    linear_combination -(k : ℝ)*correction_balance A
  have heminus : u A*((-(k : ℝ))^2-2*first A*(-(k : ℝ)))-v A*correction A*(-(k : ℝ))=
      2*u A*(k : ℝ)^2*A.mix := by
    linear_combination (k : ℝ)*correction_balance A
  have hefun (y δ : ℝ) : phi A e δ (y*δ)=
      scaledConstraint ((k : ℝ)-1) (correction A) 0 y (nearAngle A e) (farAngle A e) δ := by
    simpa only [phi, zero_add] using constraint_scaled ((k : ℝ)-1) (correction A) 0 y (nearAngle A e) (farAngle A e) δ
  simp only [←hefun] at hplus hminus
  change Tendsto _ _ (𝓝 (u A*((k : ℝ)^2-2*first A*k)-v A*correction A*k)) at hplus
  change Tendsto _ _ (𝓝 (u A*((-(k : ℝ))^2-2*first A*(-(k : ℝ)))-v A*correction A*(-(k : ℝ)))) at hminus
  rw [heplus] at hplus
  rw [heminus] at hminus
  constructor
  · convert hplus.mul_const 2 using 1
    · ext δ
      ring
    · ring
  · convert hminus.mul_const 2 using 1
    · ext δ
      ring
    · ring

end polyak.FareyPlateau.FanAnalysis.Actual
