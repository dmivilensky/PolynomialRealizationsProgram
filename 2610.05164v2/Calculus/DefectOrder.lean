import «2610.05164v2».Calculus.ClosedInterval
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: 2610.05164v2, Lemma 16.
The order-seven estimate for all three regular normalized defect ODEs in F.1.
Use: `«2610.05164v2».Calculus.cubic_quotient_zero_of_order_seven` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.defectQuotient_smooth` (defect Quotient
smooth).
Proof chain: `«2610.05164v2».DualCertificate.Data.Admissible` — 2610.05164v2, Theorem E.1; Stability
of strict admissibility and uniform transfer of the certificate value.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace «2610.05164v2».Calculus
noncomputable section
open Set Real Filter
open scoped ContDiff Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
Constructs witnesses with the exact properties `∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (0:ℝ) 1, 0≤w t ∧ w
t≤C*t^7`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefect_order_seven` uses this bound to
establish constructs witnesses with the exact properties `∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (0:ℝ) 1,
0≤R.normalizedDefect hσ t ∧ R.normalizedDefect hσ t≤C*t^7`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem defect_order_seven {p w : ℝ → ℝ} {a : ℝ} (ha : 0≤a)
    (hp : ContinuousOn p (Icc (0:ℝ) 1)) (hpn : ∀ t ∈ Icc (0:ℝ) 1, 0≤p t)
    (hw : ContinuousOn w (Icc (0:ℝ) 1)) (hzero : w 0=0)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, w t ∈ Icc (0:ℝ) (t^3))
    (hd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt w
      (p t*((1+a)*t^6-2*(1+a*t^3)*w t+a*(w t)^2)) t) :
    ∃ C : ℝ, 0<C ∧ ∀ t ∈ Icc (0:ℝ) 1, 0≤w t ∧ w t≤C*t^7 := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hp
  let C := (|M|+1)*(1+a)
  have hC : 0<C := mul_pos (by positivity) (by linarith)
  have hupper : ∀ t ∈ Ioo (0:ℝ) 1,
      p t*((1+a)*t^6-2*(1+a*t^3)*w t+a*(w t)^2)≤C*t^6 := by
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    have hwb := hb t ht'
    have hneg : -2*(1+a*t^3)*w t+a*(w t)^2≤0 := by
      have h := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha hwb.1)
        (show w t-2*t^3≤0 by linarith [hwb.2,pow_nonneg ht.1.le 3])
      nlinarith [hwb.1]
    have hpb : p t≤|M|+1 := by
      have h := hM t ht'
      rw [Real.norm_eq_abs] at h
      exact (le_abs_self _).trans (h.trans (by linarith [le_abs_self M]))
    calc
      _ ≤ p t*((1+a)*t^6) := mul_le_mul_of_nonneg_left (by linarith) (hpn t ht')
      _ ≤ (|M|+1)*((1+a)*t^6) := mul_le_mul_of_nonneg_right hpb (by positivity)
      _ = C*t^6 := by dsimp only [C]; ring
  have hD : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt (fun t => C*t^7-w t)
      (7*C*t^6-p t*((1+a)*t^6-2*(1+a*t^3)*w t+a*(w t)^2)) t := by
    intro t ht
    convert! (((hasDerivAt_id t).pow 7).const_mul C).sub (hd t ht) using 1
    simp only [id_eq]
    ring
  have hmono : MonotoneOn (fun t => C*t^7-w t) (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      ((continuousOn_const.mul (continuousOn_id.pow 7)).sub hw)
    · intro t ht
      rw [interior_Icc] at ht
      exact (hD t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      change 0≤deriv (fun t => C*t^7-w t) t
      rw [(hD t ht).deriv]
      have hpow : 0≤C*t^6 := mul_nonneg hC.le (pow_nonneg ht.1.le 6)
      linarith [hupper t ht]
  refine ⟨C,hC,fun t ht => ⟨(hb t ht).1,?_⟩⟩
  have h := hmono (by norm_num : (0:ℝ) ∈ Icc 0 1) ht ht.1
  simp only [zero_pow (by decide : 7≠0),mul_zero,hzero,sub_zero] at h
  linarith

/--
The order-seven estimate fixes the value of any continuous cubic quotient at the singular
endpoint, rather than leaving that value arbitrary.

Exact identity `g 0=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefectQuotient_zero` uses this
identity to establish the identity `R.normalizedDefectQuotient hσ 0=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem cubic_quotient_zero_of_order_seven {f g : ℝ → ℝ} {C : ℝ}
    (hg : ContinuousOn g (Icc (0:ℝ) 1))
    (hfactor : ∀ t ∈ Icc (0:ℝ) 1, f t=t^3*g t)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, 0≤f t ∧ f t≤C*t^7) : g 0=0 := by
  -- Record the convergence hl with its source filter and target limit before taking limits in
  -- the subsequent identities/bounds.
  have hl : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (g 0)) :=
    ((continuousWithinAt_Icc_iff_Ici (by norm_num : (0:ℝ)<1)).mp (hg 0 (by norm_num))).mono Ioi_subset_Ici_self
  have hnonneg : ∀ᶠ t in 𝓝[>] (0:ℝ), 0≤g t := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    have h := (hb t ⟨ht.1.le,ht.2.le⟩).1
    rw [hfactor t ⟨ht.1.le,ht.2.le⟩] at h
    exact nonneg_of_mul_nonneg_right h (pow_pos ht.1 3)
  have hupper : ∀ᶠ t in 𝓝[>] (0:ℝ), g t≤C*t^4 := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
    have h := (hb t ⟨ht.1.le,ht.2.le⟩).2
    rw [hfactor t ⟨ht.1.le,ht.2.le⟩] at h
    apply (mul_le_mul_iff_right₀ (pow_pos ht.1 3)).mp
    nlinarith [h]
  -- Record the convergence hzero with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hzero : Tendsto g (𝓝[>] (0:ℝ)) (𝓝 0) := squeeze_zero' hnonneg hupper
    (by simpa using (((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).pow 4).const_mul C).tendsto.mono_left nhdsWithin_le_nhds)
  exact tendsto_nhds_unique hl hzero

end
end «2610.05164v2».Calculus
