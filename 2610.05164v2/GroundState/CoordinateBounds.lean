import «2610.05164v2».GroundState.CoordinateLimits

/-!
Article: 2610.05164v2, Theorem 3.1.
The precise Lipschitz bound in Theorem 3.1 for a bounded density.
Use: `«2610.05164v2».GroundState.RiccatiData.q_antitone_right` feeds
`«2610.05164v2».GroundState.RiccatiData.q_two_right` (q two right).
-/
namespace «2610.05164v2».GroundState
noncomputable section
open «2610.05164v2».Continuum «2610.05164v2».Sobolev Set MeasureTheory Real Filter
open scoped InnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false

namespace RiccatiData
variable {m : ℝ → ℝ} {c : ℝ} (R : RiccatiData m c)

/--
The stated quantitative bound `R.Q x ≤ 1`.

Use: `«2610.05164v2».GroundState.RiccatiData.q_lipschitz` uses this bound to establish the
displayed Lipschitz bound: `LipschitzWith (Real.toNNReal (c*B+1)) R.q`.

Article: 2610.05164v2, Theorem 3.1 via `«2610.05164v2».GroundState.RiccatiData.q_lipschitz`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem Q_le_one (x : ℝ) : R.Q x ≤ 1 := by
  dsimp [Q,q]
  nlinarith [sq_nonneg (R.a x)]

/--
The precise Lipschitz bound in Theorem 3.1 for a bounded density.

The displayed Lipschitz bound: `LipschitzWith (Real.toNNReal (c*B+1)) R.q`.

Use: `«2610.05164v2».GroundState.GroundWitness.coordinate_lipschitz` uses this assertion to
establish the displayed Lipschitz bound: `LipschitzWith (Real.toNNReal (groundParameter hm
hn*B+1)) G.q`.

Article: 2610.05164v2, Theorem 3.1.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.RiccatiData.Q_le_one`,
`«2610.05164v2».GroundState.RiccatiData.Q_nonneg`,
`«2610.05164v2».Sobolev.locallyAC_integral_eq_sub` with the arguments shown in the proof.
-/
theorem q_lipschitz {B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hmn : ∀ x, 0 ≤ m x) (hmb : ∀ x, m x ≤ B) :
    LipschitzWith (Real.toNNReal (c*B+1)) R.q := by
  -- Use the identities/estimates `«2610.05164v2».GroundState.RiccatiData.Q_le_one`,
  -- `«2610.05164v2».GroundState.RiccatiData.Q_nonneg`,
  -- `«2610.05164v2».Sobolev.locallyAC_integral_eq_sub` with the arguments shown in the proof.
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hb (t : ℝ) : ‖c*m t-R.Q t‖ ≤ c*B+1 := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    have hcm := mul_le_mul_of_nonneg_left (hmb t) hc
    have hcn := mul_nonneg hc (hmn t)
    constructor <;> linarith [R.Q_nonneg t,R.Q_le_one t]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := x) (b := y) (fun t _ => hb t)
  rw [locallyAC_integral_eq_sub R.q_locallyAC R.q_derivative_ae] at hi
  rw [dist_comm (R.q x) (R.q y),dist_eq_norm,Real.dist_eq,
    Real.coe_toNNReal _ (by positivity),abs_sub_comm x y]
  exact hi

/--
Monotonicity in decreasing order: `AntitoneOn R.q (Iic b)`.

Use: `«2610.05164v2».GroundState.RiccatiData.q_zero_left` uses this assertion to establish
exact identity `R.q x=0`.

Article: 2610.05164v2, Theorem 3.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem q_antitone_left {b : ℝ} (hzero : ∀ x < b, m x=0) :
    AntitoneOn R.q (Iic b) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  intro x hx y hy hxy
  have hi : (∫ t in x..y, c*m t-R.Q t) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hxy]
    apply integral_nonpos_of_ae
    have hne : ∀ᵐ t ∂volume, t ≠ b := by simp [ae_iff]
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae hne] with t ht htb
    rw [hzero t (lt_of_le_of_ne (ht.2.trans hy) htb),mul_zero,zero_sub]
    exact neg_nonpos.mpr (R.Q_nonneg t)
  rw [locallyAC_integral_eq_sub R.q_locallyAC R.q_derivative_ae] at hi
  linarith

/--
Monotonicity in decreasing order: `AntitoneOn R.q (Ici b)`.

Use: `«2610.05164v2».GroundState.RiccatiData.q_two_right` uses this assertion to establish
exact identity `R.q x=2`.

Article: 2610.05164v2, Theorem 3.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem q_antitone_right {b : ℝ} (hzero : ∀ x, b < x → m x=0) :
    AntitoneOn R.q (Ici b) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  intro x hx y hy hxy
  have hi : (∫ t in x..y, c*m t-R.Q t) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hxy]
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [hzero t (hx.trans_lt ht.1),mul_zero,zero_sub]
    exact neg_nonpos.mpr (R.Q_nonneg t)
  rw [locallyAC_integral_eq_sub R.q_locallyAC R.q_derivative_ae] at hi
  linarith

/--
Exact identity `R.q x=0`.

Use: `«2610.05164v2».GroundState.GroundWitness.coordinate_support` uses this identity to
establish exact identity `(∀ x ≤ a, G.q x=0) ∧ (∀ x, b ≤ x → G.q x=2)`.

Article: 2610.05164v2, Theorem 3.1.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem q_zero_left {b : ℝ} (hzero : ∀ x < b, m x=0)
    (hlim : Tendsto R.q atBot (𝓝 0)) {x : ℝ} (hx : x ≤ b) : R.q x=0 := by
  have ha := R.q_antitone_left hzero
  have hle : ∀ᶠ y in atBot, R.q x ≤ R.q y :=
    (eventually_le_atBot x).mono (fun y hy => ha (hy.trans hx) hx hy)
  exact le_antisymm (ge_of_tendsto hlim hle) (R.q_mem x).1

/--
Exact identity `R.q x=2`.

Use: `«2610.05164v2».GroundState.GroundWitness.coordinate_support` uses this identity to
establish exact identity `(∀ x ≤ a, G.q x=0) ∧ (∀ x, b ≤ x → G.q x=2)`.

Article: 2610.05164v2, Theorem 3.1.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem q_two_right {b : ℝ} (hzero : ∀ x, b < x → m x=0)
    (hlim : Tendsto R.q atTop (𝓝 2)) {x : ℝ} (hx : b ≤ x) : R.q x=2 := by
  have ha := R.q_antitone_right hzero
  have hle : ∀ᶠ y in atTop, R.q y ≤ R.q x :=
    (eventually_ge_atTop x).mono (fun y hy => ha hx (hx.trans hy) hy)
  exact le_antisymm (R.q_mem x).2 (le_of_tendsto hlim hle)

end RiccatiData
end
end «2610.05164v2».GroundState
