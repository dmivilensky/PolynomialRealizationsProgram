import chebyshev2.PrescribedSpeed.Density

/-!
Article: chebyshev2, Theorem 5.1.
Exact exponential tail, including the support endpoint.
Use: `chebyshev2.PrescribedSpeed.SpeedData.u_ode` feeds
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density` (Theorem 5.1's prescribed
parameter is the actual spectral/variational ground parameter, rather than just a parameter of a
differential equation).
Proof chain: `chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density` — chebyshev2,
Theorem 5.1; General measurable speed gives a density with the prescribed ground parameter.
-/
namespace chebyshev2.PrescribedSpeed
noncomputable section
open chebyshev2.GroundState chebyshev2.Sobolev Set MeasureTheory Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace SpeedData
variable (S : SpeedData)

/--
Defines `A` of type `ℝ` by `∫ t in (0:ℝ)..x, 1-S.q t`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.A_difference` uses this definition to establish
exact identity `S.A b-S.A a=∫ t in a..b, 1-S.q t`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.
-/
def A (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, 1-S.q t
/--
Defines `u` of type `ℝ` by `exp (S.A x)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.d` uses this definition in the displayed
construction of `d`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.
-/
def u (x : ℝ) : ℝ := exp (S.A x)
/--
Defines `d` of type `ℝ` by `(1-S.q x)*S.u x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.d_memLp` rewrites with this definition to
establish the precise assertion is `MemLp S.d 2 volume`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.
-/
def d (x : ℝ) : ℝ := (1-S.q x)*S.u x

/--
The actual derivative at the stated point: `HasDerivAt S.A (1-S.q x) x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.A_continuous` uses this derivative formula to
establish continuity of the displayed function: `Continuous S.A`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem A_derivative (x : ℝ) : HasDerivAt S.A (1-S.q x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_const.sub S.q_continuous).intervalIntegrable 0 x)
    (continuous_const.sub S.q_continuous).stronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_const.sub S.q_continuous).continuousAt

/--
Continuity of the displayed function: `Continuous S.A`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.u_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous S.u`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.A_derivative`
with the arguments shown in the proof.
-/
theorem A_continuous : Continuous S.A := continuous_iff_continuousAt.mpr
  (fun x => (S.A_derivative x).continuousAt)
/--
The stated quantitative bound `0 < S.u x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.exponential_ground_state` uses this bound to
establish constructs witnesses with the exact properties `∃ c : ℝ, 0 < c ∧ S.u=fun x =>
c*H1.rep G.u x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem u_positive (x : ℝ) : 0 < S.u x := exp_pos _
/--
Continuity of the displayed function: `Continuous S.u`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.d_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous S.d`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.A_continuous`
with the arguments shown in the proof.
-/
theorem u_continuous : Continuous S.u := continuous_exp.comp S.A_continuous
/--
Continuity of the displayed function: `Continuous S.d`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.d_memLp` uses this continuity result to
establish the precise assertion is `MemLp S.d 2 volume`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.u_continuous` with the arguments shown in the proof.
-/
theorem d_continuous : Continuous S.d := (continuous_const.sub S.q_continuous).mul S.u_continuous

/--
The actual derivative at the stated point: `HasDerivAt S.u (S.d x) x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.u_c1` uses this derivative formula to establish
smoothness to the stated order: `ContDiff ℝ 1 S.u`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.A_derivative`
with the arguments shown in the proof.
-/
theorem u_derivative (x : ℝ) : HasDerivAt S.u (S.d x) x := by
  change HasDerivAt (fun x => exp (S.A x)) ((1-S.q x)*exp (S.A x)) x
  convert (S.A_derivative x).exp using 1
  ring

/--
Smoothness to the stated order: `ContDiff ℝ 1 S.u`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.u_locallyAC` uses this assertion to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval S.u a b`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem u_c1 : ContDiff ℝ 1 S.u := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (S.u_derivative x).differentiableAt,?_⟩
  have he : deriv S.u=S.d := funext (fun x => (S.u_derivative x).deriv)
  rw [he]
  exact S.d_continuous

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval S.u a b`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.d_locallyAC` uses this assertion to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval S.d a b`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.u_c1` with the
arguments shown in the proof.
-/
theorem u_locallyAC (a b : ℝ) : AbsolutelyContinuousOnInterval S.u a b :=
  (S.u_c1.contDiffOn : ContDiffOn ℝ 1 S.u (uIcc a b)).absolutelyContinuousOnInterval

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval S.d a b`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.exponential_ground_state` uses this assertion to
establish constructs witnesses with the exact properties `∃ c : ℝ, 0 < c ∧ S.u=fun x =>
c*H1.rep G.u x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_locallyAC`,
`chebyshev2.PrescribedSpeed.SpeedData.u_locallyAC` with the arguments shown in the proof.
-/
theorem d_locallyAC (a b : ℝ) : AbsolutelyContinuousOnInterval S.d a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1:ℝ)) a b :=
    (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => (1:ℝ)) (uIcc a b)).absolutelyContinuousOnInterval
  exact (hc.sub (S.q_locallyAC a b)).mul (S.u_locallyAC a b)

/--
Exact identity `S.A b-S.A a=∫ t in a..b, 1-S.q t`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.u_left` uses this identity to establish exact
identity `S.u x=exp (S.A (S.X 0)-S.X 0)*exp x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_continuous`
with the arguments shown in the proof.
-/
theorem A_difference (a b : ℝ) : S.A b-S.A a=∫ t in a..b, 1-S.q t := by
  have hc : Continuous (fun x => 1-S.q x) := continuous_const.sub S.q_continuous
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 a) (hc.intervalIntegrable (μ := volume) a b)
  dsimp [A]
  linarith

/--
Exact exponential tail, including the support endpoint.

Exact identity `S.u x=exp (S.A (S.X 0)-S.X 0)*exp x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.u_square_integrable` rewrites with this identity
to establish integrability of the displayed function: `Integrable (fun x => S.u x^2)`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_zero_left`,
`chebyshev2.PrescribedSpeed.SpeedData.A_difference` with the arguments shown in the proof.
-/
theorem u_left {x : ℝ} (hx : x ≤ S.X 0) : S.u x=exp (S.A (S.X 0)-S.X 0)*exp x := by
  -- Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_zero_left`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.A_difference` with the arguments shown in the
  -- proof.
  have hi : (∫ t in x..S.X 0, 1-S.q t)=S.X 0-x := by
    have he : (∫ t in x..S.X 0, 1-S.q t)=∫ _t in x..S.X 0, (1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hx] at ht
      change 1-S.q t=1
      rw [S.q_zero_left ht.2,sub_zero]
    rw [he,intervalIntegral.integral_const,smul_eq_mul,mul_one]
  have hA := S.A_difference x (S.X 0)
  rw [hi] at hA
  rw [u,← exp_add]
  congr 1
  linarith

/--
Exact identity `S.u x=exp (S.A (S.X 2)+S.X 2)*exp (-x)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.u_square_integrable` rewrites with this identity
to establish integrability of the displayed function: `Integrable (fun x => S.u x^2)`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_two_right`,
`chebyshev2.PrescribedSpeed.SpeedData.A_difference` with the arguments shown in the proof.
-/
theorem u_right {x : ℝ} (hx : S.X 2 ≤ x) : S.u x=exp (S.A (S.X 2)+S.X 2)*exp (-x) := by
  -- Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_two_right`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.A_difference` with the arguments shown in the
  -- proof.
  have hi : (∫ t in S.X 2..x, 1-S.q t)=-(x-S.X 2) := by
    have he : (∫ t in S.X 2..x, 1-S.q t)=∫ _t in S.X 2..x, (-1:ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hx] at ht
      change 1-S.q t=-1
      rw [S.q_two_right ht.1]
      norm_num
    rw [he,intervalIntegral.integral_const,smul_eq_mul,mul_neg_one]
  have hA := S.A_difference (S.X 2) x
  rw [hi] at hA
  rw [u,← exp_add]
  congr 1
  linarith

/--
Integrability of the displayed function: `Integrable (fun x => S.u x^2)`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.u_memLp` uses this integrability result to
establish the precise assertion is `MemLp S.u 2 volume`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.u_left`,
`chebyshev2.PrescribedSpeed.SpeedData.u_right`,
`chebyshev2.PrescribedSpeed.SpeedData.u_continuous` with the arguments shown in the proof.
-/
theorem u_square_integrable : Integrable (fun x => S.u x^2) := by
  -- Establish hl as the integrability justification for the later integral estimates or
  -- changes of order.
  have hl : IntegrableOn (fun x => S.u x^2) (Iic (S.X 0)) := by
    have h := (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<2) (S.X 0)).const_mul
      (exp (S.A (S.X 0)-S.X 0)^2)
    apply IntegrableOn.congr_fun h _ measurableSet_Iic
    intro x hx
    dsimp only
    rw [S.u_left hx,mul_pow]
    congr 1
    exact exp_nat_mul x 2
  -- Establish hr as the integrability justification for the later integral estimates or
  -- changes of order.
  have hr : IntegrableOn (fun x => S.u x^2) (Ioi (S.X 2)) := by
    have h := (integrableOn_exp_mul_Ioi (by norm_num : (-2:ℝ)<0) (S.X 2)).const_mul
      (exp (S.A (S.X 2)+S.X 2)^2)
    apply IntegrableOn.congr_fun h _ measurableSet_Ioi
    intro x hx
    dsimp only
    rw [S.u_right hx.le,mul_pow]
    congr 1
    simpa only [Nat.cast_ofNat,mul_neg,neg_mul] using exp_nat_mul (-x) 2
  -- Establish hm as the integrability justification for the later integral estimates or
  -- changes of order.
  have hm : IntegrableOn (fun x => S.u x^2) (Icc (S.X 0) (S.X 2)) :=
    (S.u_continuous.pow 2).integrableOn_Icc
  have hi := (hl.union hm).union hr
  rw [Iic_union_Icc_eq_Iic S.X_endpoint_order.le,Iic_union_Ioi,integrableOn_univ] at hi
  exact hi

/--
The precise assertion is `MemLp S.u 2 volume`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.d_memLp` uses this assertion to establish the
precise assertion is `MemLp S.d 2 volume`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.u_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.u_square_integrable` with the arguments shown in the
proof.
-/
theorem u_memLp : MemLp S.u 2 volume :=
  (memLp_two_iff_integrable_sq S.u_continuous.aestronglyMeasurable).mpr S.u_square_integrable

/--
The precise assertion is `MemLp S.d 2 volume`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.u_regular` uses this assertion to establish the
precise assertion is `SobolevRegular S.u S.d where value_memLp`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.u_memLp`,
`chebyshev2.PrescribedSpeed.SpeedData.d_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.q_mem` with the arguments shown in the proof.
-/
theorem d_memLp : MemLp S.d 2 volume := by
  apply S.u_memLp.of_le S.d_continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [d,norm_mul,Real.norm_eq_abs]
    have hb : |1-S.q x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [(S.q_mem x).1,(S.q_mem x).2]
    exact mul_le_of_le_one_left (norm_nonneg _) hb)

/--
The precise assertion is `SobolevRegular S.u S.d where value_memLp`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.exists_h1_u` uses this assertion to establish
constructs witnesses with the exact properties `∃ v : H1, H1.rep v=S.u`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.u_memLp`,
`chebyshev2.PrescribedSpeed.SpeedData.d_memLp`,
`chebyshev2.PrescribedSpeed.SpeedData.u_locallyAC` with the arguments shown in the proof.
-/
theorem u_regular : SobolevRegular S.u S.d where
  value_memLp := S.u_memLp
  derivative_memLp := S.d_memLp
  locally_ac := S.u_locallyAC
  derivative_ae := Filter.Eventually.of_forall S.u_derivative

/--
Constructs witnesses with the exact properties `∃ v : H1, H1.rep v=S.u`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.exponential_ground_state` uses this identity to
establish constructs witnesses with the exact properties `∃ c : ℝ, 0 < c ∧ S.u=fun x =>
c*H1.rep G.u x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Use the identities/estimates `chebyshev2.Sobolev.H1.range_iff`,
`chebyshev2.PrescribedSpeed.SpeedData.u_regular` with the arguments shown in the proof.
-/
theorem exists_h1_u : ∃ v : H1, H1.rep v=S.u := (H1.range_iff S.u).mpr ⟨S.d,S.u_regular⟩

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x ∂volume, HasDerivAt S.d
((1-κ*S.density κ x)*S.u x) x`.

Use: `chebyshev2.PrescribedSpeed.SpeedData.exponential_ground_state` uses this assertion to
establish constructs witnesses with the exact properties `∃ c : ℝ, 0 < c ∧ S.u=fun x =>
c*H1.rep G.u x`.

Article: chebyshev2, Theorem 5.1 via
`chebyshev2.PrescribedSpeed.SpeedData.groundParameter_density`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem u_ode {κ : ℝ} (hκ : 0 < κ) :
    ∀ᵐ x ∂volume, HasDerivAt S.d ((1-κ*S.density κ x)*S.u x) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [S.q_derivative_ae] with x hx
  have hd := ((hasDerivAt_const x (1:ℝ)).sub hx).mul (S.u_derivative x)
  change HasDerivAt S.d ((0-S.speed x)*S.u x+(1-S.q x)*S.d x) x at hd
  convert hd using 1
  rw [S.density_identity hκ]
  dsimp [Q,d]
  ring

end SpeedData
end
end chebyshev2.PrescribedSpeed
