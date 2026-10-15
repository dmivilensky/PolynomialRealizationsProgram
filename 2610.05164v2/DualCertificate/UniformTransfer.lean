import «2610.05164v2».DualCertificate.EnergyBound

/-!
Article: 2610.05164v2, Theorem 3.6.
The finite-fiber transfer in E.1: all sections of the full fiber have the same limiting
observations, and sectionwise lower bounds give uniform bounds.
Use: `«2610.05164v2».DualCertificate.gainConstant_ge_of_uniform` feeds
`«2610.05164v2».DualCertificate.Data.gainConstant_ge_value` (gain Constant ge value).
Proof chain: `«2610.05164v2».DualCertificate.Data.gainConstant_ge_value` — 2610.05164v2, Theorem
3.6; admissible certificates imply continuum, finite-fiber and gain bounds.
-/
namespace «2610.05164v2».DualCertificate
noncomputable section
open Set Filter MeasureTheory Real «2610.05164v2».Calibration «2610.05164v2».Packing «2610.05164v2».GroundState
open «2610.05164v2».Calibration.Data «2610.05164v2».Filters
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ n in atTop, ∀ a : α n, L-ε≤v
n a`.

Use: `«2610.05164v2».DualCertificate.AnalyticData.uniform_finite_lower_bound` uses this bound
to prove the eventual or almost-everywhere assertion `∀ᶠ n in atTop, ∀ J
: «2610.05164v2».Fiber (n+1), A.targetValue-ε≤J.val.normalizedEnergy`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound`.

Proof: Separate `∃ b : α n, v n b<L-ε` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Assume the failure of the desired conclusion and derive a
contradiction from the available bounds/identities. Intersect the eventual or almost-everywhere
hypotheses, then prove the asserted relation at an arbitrary point in that intersection.
-/
theorem uniform_lower_of_all_sections {α : ℕ → Type*} (inh : ∀ n, Nonempty (α n))
    {v : (n : ℕ) → α n → ℝ} {L : ℝ}
    (hv : ∀ f : (n : ℕ) → α n, Tendsto (fun n => v n (f n)) atTop (𝓝 L))
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ n in atTop, ∀ a : α n, L-ε≤v n a := by
  -- Separate `∃ b : α n, v n b<L-ε` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  have hex (n : ℕ) : ∃ a : α n, (∃ b : α n, v n b<L-ε) → v n a<L-ε := by
    by_cases h : ∃ b : α n, v n b<L-ε
    · obtain ⟨b,hb⟩ := h
      exact ⟨b,fun _ => hb⟩
    · exact ⟨Classical.choice (inh n),fun he => (h he).elim⟩
  choose f hf using hex
  have he := (hv f).eventually (lt_mem_nhds (show L-ε<L by linarith))
  filter_upwards [he] with n hn a
  by_contra ha
  have hbad := hf n ⟨a,lt_of_not_ge ha⟩
  linarith

 /--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n =>
packedLogDeterminant (J n).val (by omega) (J n).property s) atTop (𝓝 (log (cosh (sqrt s))))`.

Use: `«2610.05164v2».DualCertificate.AnalyticData.packed_value_tendsto_of_continuous` uses this
limit to establish the limit stated in that declaration.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem packed_fixed_observation_tendsto (J : ∀ n : ℕ, «2610.05164v2».Fiber (n+1))
    {s : ℝ} (hs : 0≤s) :
    Tendsto (fun n => packedLogDeterminant (J n).val (by omega) (J n).property s)
      atTop (𝓝 (log (cosh (sqrt s)))) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  have hd := transferError_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  -- Record the convergence hz with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hz : Tendsto (fun n : ℕ => s/2*transferError (n+1)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using hd.const_mul (s/2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hz
  exact Eventually.of_forall (fun n => by
    simpa only [Real.norm_eq_abs] using
      packed_logDeterminant_distance (J n).val (by omega) (J n).property hs)

 /--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n => ∑' j,
(packedEigenvalue (J n).val (by omega) (J n).property j)^2) atTop (𝓝 (2/3:ℝ))`.

Use: `«2610.05164v2».DualCertificate.packed_S_tendsto` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto (fun n => (packedCoupling (J
n).val (by omega) (J n).property)^2/4* ∑' j, (packedEigenvalue (J n).val (by omega) (J
n).property j)^2) atTop (𝓝 ((Real.pi^2/4)^2/6))`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem packed_trace_tendsto (J : ∀ n : ℕ, «2610.05164v2».Fiber (n+1)) :
    Tendsto (fun n => ∑' j, (packedEigenvalue (J n).val (by omega) (J n).property j)^2)
      atTop (𝓝 (2/3:ℝ)) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  have hd := transferError_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  -- Record the convergence hz with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hz : Tendsto (fun n : ℕ => 2*transferError (n+1)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using hd.const_mul 2
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hz
  exact Eventually.of_forall (fun n => by
    simpa only [Real.norm_eq_abs] using
      packed_square_trace_distance (J n).val (by omega) (J n).property)

 /--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n =>
(packedCoupling (J n).val (by omega) (J n).property)^2/4* ∑' j, (packedEigenvalue (J n).val (by
omega) (J n).property j)^2) atTop (𝓝 ((Real.pi^2/4)^2/6))`.

Use: `«2610.05164v2».DualCertificate.AnalyticData.packed_value_tendsto_of_continuous` uses this
limit to establish the limit stated in that declaration.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.packedCoupling_tendsto`,
`«2610.05164v2».DualCertificate.packed_trace_tendsto` with the arguments shown in the proof.
-/
theorem packed_S_tendsto (J : ∀ n : ℕ, «2610.05164v2».Fiber (n+1)) :
    Tendsto (fun n => (packedCoupling (J n).val (by omega) (J n).property)^2/4*
      ∑' j, (packedEigenvalue (J n).val (by omega) (J n).property j)^2)
      atTop (𝓝 ((Real.pi^2/4)^2/6)) := by
  convert! (((Data.packedCoupling_tendsto J).pow 2).div_const 4).mul
    (packed_trace_tendsto J) using 1
  congr 1
  ring

namespace AnalyticData
variable (A : AnalyticData)

 /--
The stated quantitative bound `A.value (packedCoupling_positive J hN ht) (packedLogDeterminant
J hN ht 32) (packedLogDeterminant J hN ht 64) (packedLogDeterminant J hN ht
(A.calibration.sigma*packedCoupling J hN ht)) ((packedCoupling J hN ht)^2/4*∑' j,
packedEigenvalue J hN ht j^2) ≤ J.normalizedEnergy`.

Use: `«2610.05164v2».DualCertificate.AnalyticData.uniform_finite_lower_bound` uses this bound
to prove the eventual or almost-everywhere assertion `∀ᶠ n in atTop, ∀ J
: «2610.05164v2».Fiber (n+1), A.targetValue-ε≤J.val.normalizedEnergy`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem packed_energy_ge_value {N : ℕ} (J : «2610.05164v2».Jacobi N) (hN : 0<N)
    (ht : J.Terminal) (ha : A.Admissible (packedCoupling_positive J hN ht)) :
    A.value (packedCoupling_positive J hN ht)
      (packedLogDeterminant J hN ht 32) (packedLogDeterminant J hN ht 64)
      (packedLogDeterminant J hN ht (A.calibration.sigma*packedCoupling J hN ht))
      ((packedCoupling J hN ht)^2/4*∑' j, packedEigenvalue J hN ht j^2) ≤
        J.normalizedEnergy := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let P := packing J hN ht
  let hm := (P.blocks hN).closedDensity_integrable
  let hn := (P.blocks hN).closedDensity_nonneg
  have hM : (∫ x, (P.blocks hN).closedDensity x)=1 := P.density_mass hN ht
  have hne : ¬ (P.blocks hN).closedDensity=ᵐ[volume] 0 := by
    intro he
    have hz := integral_congr_ae he
    simp only [Pi.zero_apply,integral_zero] at hz
    linarith
  let G := Classical.choice (ground_state hm hn hne)
  have h := A.energy_ge_value G ha hM
    (sqrt_cube_integrable_of_bounded hm hn ((P.blocks hN).closedDensity_bound))
  have he : (fun x => (sqrt ((P.blocks hN).closedDensity x))^3)=
      fun x => packedDensity J hN ht x^(3/2:ℝ) :=
    funext (fun x => «2610.05164v2».Calibration.sqrt_cube_eq_rpow (hn x))
  rw [he,packedDensity_energy J hN ht,linear_square_trace hm hn] at h
  exact h

/--
E.1's uniform conclusion once persistence of admissibility and convergence of the analytic
value have been established for the certificate.

Establishes the stated eventual or almost-everywhere assertion `∀ᶠ n in atTop, ∀ J :
«2610.05164v2».Fiber (n+1), A.targetValue-ε≤J.val.normalizedEnergy`.

Use: `«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound` uses this bound to
establish establishes the stated eventual or almost-everywhere assertion `∀ᶠ n in atTop,∀ J :
«2610.05164v2».Fiber (n+1),D.analytic.targetValue-ε≤J.val.normalizedEnergy`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem uniform_finite_lower_bound
    (hstable : ∀ᶠ κ in 𝓝 (Real.pi^2/4), ∀ hκ : 0<κ, A.Admissible hκ)
    (hvalue : ∀ J : ∀ n : ℕ, «2610.05164v2».Fiber (n+1),
      Tendsto (fun n => A.value (packedCoupling_positive (J n).val (by omega) (J n).property)
        (packedLogDeterminant (J n).val (by omega) (J n).property 32)
        (packedLogDeterminant (J n).val (by omega) (J n).property 64)
        (packedLogDeterminant (J n).val (by omega) (J n).property
          (A.calibration.sigma*packedCoupling (J n).val (by omega) (J n).property))
        ((packedCoupling (J n).val (by omega) (J n).property)^2/4*
          ∑' j, packedEigenvalue (J n).val (by omega) (J n).property j^2))
        atTop (𝓝 A.targetValue)) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n in atTop, ∀ J : «2610.05164v2».Fiber (n+1), A.targetValue-ε≤J.val.normalizedEnergy := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  classical
  let V := fun n (J : «2610.05164v2».Fiber (n+1)) =>
    if A.Admissible (packedCoupling_positive J.val (by omega) J.property) then
      A.value (packedCoupling_positive J.val (by omega) J.property)
        (packedLogDeterminant J.val (by omega) J.property 32)
        (packedLogDeterminant J.val (by omega) J.property 64)
        (packedLogDeterminant J.val (by omega) J.property
          (A.calibration.sigma*packedCoupling J.val (by omega) J.property))
        ((packedCoupling J.val (by omega) J.property)^2/4*
          ∑' j, packedEigenvalue J.val (by omega) J.property j^2)
    else J.val.normalizedEnergy
  have hv : ∀ J : ∀ n : ℕ, «2610.05164v2».Fiber (n+1), Tendsto (fun n => V n (J n))
      atTop (𝓝 A.targetValue) := by
    intro J
    apply (hvalue J).congr'
    filter_upwards [(Data.packedCoupling_tendsto J).eventually hstable] with n hn
    exact (ite_eq_left (hn (packedCoupling_positive (J n).val (by omega) (J n).property))).symm
  have hb : ∀ n (J : «2610.05164v2».Fiber (n+1)), V n J≤J.val.normalizedEnergy := by
    intro n J
    dsimp only [V]
    split_ifs with h
    · exact A.packed_energy_ge_value J.val (by omega) J.property h
    · exact le_rfl
  filter_upwards [uniform_lower_of_all_sections
    (fun n => ⟨«2610.05164v2».SineJacobi.fiber (n+1) (by omega)⟩) hv hε] with n hn J
  exact (hn J).trans (hb n J)

end AnalyticData

/--
The uniform finite estimate implies the article's liminf Green bound.

The stated quantitative bound `L≤«2610.05164v2».Optimal.greenConstant`.

Use: `«2610.05164v2».DualCertificate.gainConstant_ge_of_uniform` uses this bound to establish
the stated quantitative bound `2*sqrt L≤«2610.05164v2».Optimal.gainConstant I`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.greenConstant_ge_value`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem greenConstant_ge_of_uniform {L : ℝ}
    (hL : ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop,
      ∀ J : «2610.05164v2».Fiber (n+1), L-ε≤J.val.normalizedEnergy) :
    L≤«2610.05164v2».Optimal.greenConstant := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  open «2610.05164v2».Optimal in
  apply (le_liminf_iff energy_bounded_above.isCoboundedUnder_ge energy_bounded_below).2
  intro y hy
  have he := hL ((L-y)/2) (by linarith)
  filter_upwards [he] with n hn
  have hb : L-(L-y)/2≤«2610.05164v2».Optimal.finiteEnergy n := by
    apply le_csInf («2610.05164v2».Optimal.energyValues_nonempty n)
    rintro _ ⟨J,rfl⟩
    exact hn J
  linarith

 /--
The stated quantitative bound `2*sqrt L≤«2610.05164v2».Optimal.gainConstant I`.

Use: `«2610.05164v2».DualCertificate.Data.gainConstant_ge_value` uses this bound to establish
the stated quantitative bound `2*sqrt
D.analytic.targetValue≤«2610.05164v2».Optimal.gainConstant I`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.gainConstant_ge_value`.

Proof: Use the identities/estimates
`«2610.05164v2».DualCertificate.greenConstant_ge_of_uniform`,
`«2610.05164v2».Optimal.gainConstant_lower` with the arguments shown in the proof.
-/
theorem gainConstant_ge_of_uniform {L : ℝ}
    (hL : ∀ ε : ℝ, 0<ε → ∀ᶠ n in atTop,
      ∀ J : «2610.05164v2».Fiber (n+1), L-ε≤J.val.normalizedEnergy)
    (I : «2606.16671v2».SpectralInterval) : 2*sqrt L≤«2610.05164v2».Optimal.gainConstant I :=
  (mul_le_mul_of_nonneg_left (sqrt_le_sqrt (greenConstant_ge_of_uniform hL))
    (by norm_num)).trans («2610.05164v2».Optimal.gainConstant_lower I)

end
end «2610.05164v2».DualCertificate
