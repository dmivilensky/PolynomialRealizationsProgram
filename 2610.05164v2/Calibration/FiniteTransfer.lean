import «2610.05164v2».Calibration.OneDeterminant

/-!
Article: 2610.05164v2, Proposition 6.
Proposition 6 for the liminf over the full finite fiber.
Result: `«2610.05164v2».Calibration.Data.greenConstant_ge_referenceBase` supplies the stated article
conclusion.
-/
namespace «2610.05164v2».Calibration
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Packing «2610.05164v2».Optimal
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace Data
variable (C : Data)

/--
Defines `referenceBase` of type `ℝ` by `C.base (Real.pi^2/4) (log (cosh (sqrt
(C.sigma*(Real.pi^2/4)))))`.

Use: `«2610.05164v2».Calibration.Data.greenConstant_ge_referenceBase` uses this definition to
establish the stated quantitative bound `C.referenceBase ≤ greenConstant`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def referenceBase : ℝ := C.base (Real.pi^2/4) (log (cosh (sqrt (C.sigma*(Real.pi^2/4)))))

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n =>
packedCoupling (J n).val (by omega) (J n).property) atTop (𝓝 (Real.pi^2/4))`.

Use: `«2610.05164v2».Calibration.Data.packedBase_tendsto` uses this limit to establish the
limit stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.uniform_finite_lower_bound`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem packedCoupling_tendsto (J : ∀ n : ℕ, «2610.05164v2».Fiber (n+1)) :
    Tendsto (fun n => packedCoupling (J n).val (by omega) (J n).property) atTop (𝓝 (Real.pi^2/4)) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  have hd := transferError_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  have he : ∀ᶠ n : ℕ in atTop, transferError (n+1)<«2610.05164v2».Continuum.referenceEigenvalue 0/2 :=
    hd.eventually (gt_mem_nhds (div_pos («2610.05164v2».Continuum.referenceEigenvalue_pos 0) (by norm_num) : (0:ℝ)<«2610.05164v2».Continuum.referenceEigenvalue 0/2))
  -- Record the convergence hz with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hz : Tendsto (fun n : ℕ => 4*transferError (n+1)/(«2610.05164v2».Continuum.referenceEigenvalue 0)^2)
      atTop (𝓝 0) := by
    convert (hd.const_mul 4).div_const ((«2610.05164v2».Continuum.referenceEigenvalue 0)^2) using 1 <;> norm_num
  have hb : ∀ᶠ n : ℕ in atTop,
      ‖packedCoupling (J n).val (by omega) (J n).property-Real.pi^2/4‖ ≤
        4*transferError (n+1)/(«2610.05164v2».Continuum.referenceEigenvalue 0)^2 := by
    filter_upwards [he] with n hn
    exact packed_ground_parameter_distance (J n).val (by omega) (J n).property hn
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr
    (by simpa only [Real.norm_eq_abs,abs_zero] using (squeeze_zero_norm' hb hz).norm)

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n =>
packedLogDeterminant (J n).val (by omega) (J n).property (C.sigma*packedCoupling (J n).val (by
omega) (J n).property)) atTop (𝓝 (log (cosh (sqrt (C.sigma*(Real.pi^2/4))))))`.

Use: `«2610.05164v2».Calibration.Data.packedBase_tendsto` uses this limit to establish the
limit stated in that declaration.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
-/
theorem packedObservation_tendsto (J : ∀ n : ℕ, «2610.05164v2».Fiber (n+1)) :
    Tendsto (fun n => packedLogDeterminant (J n).val (by omega) (J n).property
      (C.sigma*packedCoupling (J n).val (by omega) (J n).property)) atTop
        (𝓝 (log (cosh (sqrt (C.sigma*(Real.pi^2/4)))))) := by
  -- Pass the established inequalities to the limit using the displayed filter convergence.
  let k : ℝ := Real.pi^2/4
  let κ := fun n => packedCoupling (J n).val (by omega) (J n).property
  have hk : 0 < k := by dsimp [k]; exact div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num)
  have hκ : ∀ n, 0 < κ n := fun n => packedCoupling_positive (J n).val (by omega) (J n).property
  have hd := transferError_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  -- Record the convergence hkl with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hkl : Tendsto κ atTop (𝓝 k) := packedCoupling_tendsto J
  -- Record the convergence hz with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hz : Tendsto (fun n : ℕ => C.sigma/2*|κ n-k|+C.sigma*k/2*transferError (n+1)) atTop (𝓝 0) := by
    convert (((hkl.sub_const k).abs).const_mul (C.sigma/2)).add
      (hd.const_mul (C.sigma*k/2)) using 1 <;> norm_num
  have hb : ∀ᶠ n : ℕ in atTop,
      ‖packedLogDeterminant (J n).val (by omega) (J n).property (C.sigma*κ n)-
        log (cosh (sqrt (C.sigma*k)))‖ ≤ C.sigma/2*|κ n-k|+C.sigma*k/2*transferError (n+1) := by
    apply Eventually.of_forall
    intro n
    have hs : 0 ≤ C.sigma*κ n := mul_nonneg C.sigma_positive.le (hκ n).le
    have ht : 0 ≤ C.sigma*k := mul_nonneg C.sigma_positive.le hk.le
    have h := logDeterminant_scale_distance (packedEigenvalue_summable (J n).val (by omega) (J n).property)
      (packedEigenvalue_nonneg (J n).val (by omega) (J n).property) hs ht
    rw [packedEigenvalue_mass (J n).val (by omega) (J n).property,mul_one] at h
    have he : |C.sigma*κ n-C.sigma*k|/2=C.sigma/2*|κ n-k| := by
      rw [← mul_sub,abs_mul,abs_of_pos C.sigma_positive]
      ring
    rw [he] at h
    exact (abs_sub_le _ _ _).trans (add_le_add h
      (packed_logDeterminant_distance (J n).val (by omega) (J n).property ht))
  have ht := squeeze_zero_norm' hb hz
  exact (tendsto_iff_norm_sub_tendsto_zero).mpr (by simpa only [norm_zero] using ht.norm)

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun n => C.base
(packedCoupling (J n).val (by omega) (J n).property) (packedLogDeterminant (J n).val (by omega)
(J n).property (C.sigma*packedCoupling (J n).val (by omega) (J n).property))) atTop (𝓝
C.referenceBase)`.

Use: `«2610.05164v2».Calibration.Data.greenConstant_ge_referenceBase` uses this limit to
establish the stated quantitative bound `C.referenceBase ≤ greenConstant`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.base_tendsto`,
`«2610.05164v2».Calibration.Data.packedCoupling_tendsto`,
`«2610.05164v2».Calibration.Data.packedObservation_tendsto` with the arguments shown in the
proof.
-/
theorem packedBase_tendsto (J : ∀ n : ℕ, «2610.05164v2».Fiber (n+1)) :
    Tendsto (fun n => C.base (packedCoupling (J n).val (by omega) (J n).property)
      (packedLogDeterminant (J n).val (by omega) (J n).property
        (C.sigma*packedCoupling (J n).val (by omega) (J n).property))) atTop (𝓝 C.referenceBase) :=
  C.base_tendsto (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num)) (packedCoupling_tendsto J) (C.packedObservation_tendsto J)

/--
The finite-fiber conclusion e ≥ B*, with the same constant as in (21).

The stated quantitative bound `C.referenceBase ≤ greenConstant`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Proposition 6.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem greenConstant_ge_referenceBase : C.referenceBase ≤ greenConstant := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hex (n : ℕ) : ∃ J : «2610.05164v2».Fiber (n+1),
      J.val.normalizedEnergy<finiteEnergy n+1/(n+1:ℝ) := by
    obtain ⟨a,⟨J,rfl⟩,ha⟩ := exists_lt_of_csInf_lt (energyValues_nonempty n)
      (show finiteEnergy n<finiteEnergy n+1/(n+1:ℝ) by
        have hp : 0<(1/(n+1:ℝ)) := by positivity
        linarith)
    exact ⟨J,ha⟩
  choose J hJ using hex
  have hl := C.packedBase_tendsto J
  -- Record the convergence heps with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have heps : Tendsto (fun n : ℕ => 1/(n+1:ℝ)) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hlim := hl.sub heps
  have hb : ∀ n : ℕ, C.base (packedCoupling (J n).val (by omega) (J n).property)
      (packedLogDeterminant (J n).val (by omega) (J n).property
        (C.sigma*packedCoupling (J n).val (by omega) (J n).property))-1/(n+1:ℝ) ≤ finiteEnergy n := by
    intro n
    have h := C.packed_energy_ge_base (J n).val (by omega) (J n).property
    linarith [hJ n]
  apply (le_liminf_iff energy_bounded_above.isCoboundedUnder_ge energy_bounded_below).2
  intro y hy
  have he : ∀ᶠ n : ℕ in atTop, y< C.base (packedCoupling (J n).val (by omega) (J n).property)
      (packedLogDeterminant (J n).val (by omega) (J n).property
        (C.sigma*packedCoupling (J n).val (by omega) (J n).property))-1/(n+1:ℝ) := by
    exact hlim.eventually (lt_mem_nhds (by simpa only [sub_zero] using hy))
  filter_upwards [he] with n hn
  exact hn.trans_le (hb n)

end Data
end
end «2610.05164v2».Calibration
