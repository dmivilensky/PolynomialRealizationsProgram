import «2606.16671v2».SineJacobi.LogSinc

/-!
Article: 2606.16671v2, Theorem E.3.
Uniform quantitative correction of the finite sine ratio by the half-binomial ratio.
Use: `«2606.16671v2».SineJacobi.logRatio_error_bound` feeds
`«2606.16671v2».SineJacobi.logRatio_correction_limit` (log Ratio correction limit).
Proof chain: `«2606.16671v2».SineJacobi.ratio_scaled_limit` — 2606.16671v2, Theorem E.3; Hard-edge
recurrence, singular ODE, uniqueness and endpoint limits.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Real Set

/--
Defines `logRatio` of type `ℝ` by `log (ratio N k/binomialRatio k)`.

Use: `«2606.16671v2».SineJacobi.logRatio_error_bound` uses this definition to establish the
stated quantitative bound `|logRatio N k+logSinc ((k:ℝ)/N)/2| ≤ M*(k:ℝ)/(N:ℝ)^2`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.
-/
def logRatio (N k : ℕ) : ℝ := log (ratio N k/binomialRatio k)

/--
Exact identity `logRatio N 0 = 0`.

Use: `«2606.16671v2».SineJacobi.logRatio_error_bound` uses this identity to establish the
stated quantitative bound `|logRatio N k+logSinc ((k:ℝ)/N)/2| ≤ M*(k:ℝ)/(N:ℝ)^2`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem logRatio_zero (N : ℕ) : logRatio N 0 = 0 := by simp [logRatio]

/--
Exact identity `logRatio N (k+1) = logRatio N k + logSinc (((k:ℝ)+1/2)/N) - logSinc
(((k:ℝ)+1)/N)`.

Use: `«2606.16671v2».SineJacobi.logRatio_error_bound` rewrites with this identity to establish
the stated quantitative bound `|logRatio N k+logSinc ((k:ℝ)/N)/2| ≤ M*(k:ℝ)/(N:ℝ)^2`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.ratio_sinc_recurrence`,
`«2606.16671v2».SineJacobi.sinc_angle_pos`, `«2606.16671v2».SineJacobi.binomialRatio_pos` with
the arguments shown in the proof.
-/
theorem logRatio_recurrence (N k : ℕ) (hk : k+1 < N) :
    logRatio N (k+1) = logRatio N k + logSinc (((k:ℝ)+1/2)/N) -
      logSinc (((k:ℝ)+1)/N) := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.ratio_sinc_recurrence`,
  -- `«2606.16671v2».SineJacobi.sinc_angle_pos`, `«2606.16671v2».SineJacobi.binomialRatio_pos`
  -- with the arguments shown in the proof.
  have hr := ratio_sinc_recurrence N k hk
  have hN : 0 < N := by omega
  have hc : (k:ℝ)+1 < N := by exact_mod_cast hk
  have hb := sinc_angle_pos N hN (t := (k:ℝ)+1) (by positivity) hc
  have hm := sinc_angle_pos N hN (t := (k:ℝ)+1/2) (by positivity) (by linarith)
  have hp : ((k:ℝ)+1/2) ≠ 0 := by positivity
  have hq : ((k:ℝ)+1) ≠ 0 := by positivity
  have hl := congrArg log hr
  rw [log_div (mul_ne_zero (mul_ne_zero (ratio_pos N k (by omega)).ne' hm.ne') hp) hq,
    log_mul (mul_ne_zero (ratio_pos N k (by omega)).ne' hm.ne') hp,
    log_mul (ratio_pos N k (by omega)).ne' hm.ne',
    log_mul (ratio_pos N (k+1) hk).ne' hb.ne'] at hl
  have hlb : log (binomialRatio (k+1)) =
      log (binomialRatio k)+log ((k:ℝ)+1/2)-log ((k:ℝ)+1) := by
    rw [binomialRatio, log_div (mul_ne_zero (binomialRatio_pos k).ne' hp) hq,
      log_mul (binomialRatio_pos k).ne' hp]
  unfold logRatio logSinc
  rw [log_div (ratio_pos N (k+1) hk).ne' (binomialRatio_pos _).ne',
    log_div (ratio_pos N k (by omega)).ne' (binomialRatio_pos _).ne', hlb]
  have ha (x : ℝ) : Real.pi*(x/(N:ℝ)) = x*h N := by unfold h; ring
  rw [ha, ha]
  linarith

/--
Uniform quantitative correction of the finite sine ratio by the half-binomial ratio.

The stated quantitative bound `|logRatio N k+logSinc ((k:ℝ)/N)/2| ≤ M*(k:ℝ)/(N:ℝ)^2`.

Use: `«2606.16671v2».SineJacobi.logRatio_correction_limit` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun a =>
logRatio (N a) (k a)+logSinc ((k a:ℝ)/(N a:ℝ))/2) l (𝓝 0)`.

Article: 2606.16671v2, Theorem 5.1 via `«2606.16671v2».SineJacobi.sineIntegral_eq`.

Proof: Induct on `k`; the recursive step uses the previous-stage assertion.
-/
theorem logRatio_error_bound {b M : ℝ} (_hb : 0 ≤ b) (hb1 : b < 1) (hM : 0 ≤ M)
    (hbnd : ∀ x ∈ Icc 0 b, |deriv (deriv logSinc) x| ≤ M)
    (N k : ℕ) (hk : k < N) (hkb : (k:ℝ)/N ≤ b) :
    |logRatio N k+logSinc ((k:ℝ)/N)/2| ≤ M*(k:ℝ)/(N:ℝ)^2 := by
  -- Induct on `k`; the recursive step uses the previous-stage assertion.
  have hN : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hsub : Icc (0:ℝ) b ⊆ Ioo (-1:ℝ) 1 :=
    fun x hx => ⟨by linarith [hx.1], hx.2.trans_lt hb1⟩
  have hg : ∀ x ∈ Icc (0:ℝ) b, HasDerivAt logSinc (deriv logSinc x) x := by
    intro x hx
    exact ((logSinc_contDiff.differentiableOn (by norm_num) x (hsub hx)).differentiableAt
      (isOpen_Ioo.mem_nhds (hsub hx))).hasDerivAt
  have hg' : ∀ x ∈ Icc (0:ℝ) b, HasDerivAt (deriv logSinc) (deriv (deriv logSinc) x) x := by
    intro x hx
    have h1 : ContDiffOn ℝ 1 (deriv logSinc) (Ioo (-1:ℝ) 1) :=
      logSinc_contDiff.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact ((h1.differentiableOn (by norm_num) x (hsub hx)).differentiableAt
      (isOpen_Ioo.mem_nhds (hsub hx))).hasDerivAt
  induction k with
  | zero => simp
  | succ k ih =>
    have hle : (k:ℝ)/N ≤ ((k:ℝ)+1)/N :=
      div_le_div_of_nonneg_right (by linarith) hN.le
    have hkbr : ((k:ℝ)+1)/N ≤ b := by simpa only [Nat.cast_add, Nat.cast_one] using hkb
    have hi := ih (by omega) (hle.trans hkbr)
    have hmid := «2606.16671v2».Analysis.midpoint_error_bound hle hM
      (fun x hx => hg x ⟨(div_nonneg (Nat.cast_nonneg _) hN.le).trans hx.1,
        hx.2.trans hkbr⟩)
      (fun x hx => hg' x ⟨(div_nonneg (Nat.cast_nonneg _) hN.le).trans hx.1,
        hx.2.trans hkbr⟩)
      (fun x hx => hbnd x ⟨(div_nonneg (Nat.cast_nonneg _) hN.le).trans hx.1,
        hx.2.trans hkbr⟩)
    have hmidarg : ((k:ℝ)/N+((k:ℝ)+1)/N)/2 = ((k:ℝ)+1/2)/N := by ring
    have hstep : (((k:ℝ)+1)/N-(k:ℝ)/N)^2 = 1/(N:ℝ)^2 := by ring
    rw [hmidarg, hstep] at hmid
    have ht := norm_add_le (logRatio N k+logSinc ((k:ℝ)/N)/2)
      (logSinc (((k:ℝ)+1/2)/N)-(logSinc ((k:ℝ)/N)+logSinc (((k:ℝ)+1)/N))/2)
    simp only [Real.norm_eq_abs] at ht
    rw [logRatio_recurrence N k hk]
    push_cast
    have he : logRatio N k+logSinc (((k:ℝ)+1/2)/N)-logSinc (((k:ℝ)+1)/N)+
        logSinc (((k:ℝ)+1)/N)/2 =
      (logRatio N k+logSinc ((k:ℝ)/N)/2)+
        (logSinc (((k:ℝ)+1/2)/N)-(logSinc ((k:ℝ)/N)+logSinc (((k:ℝ)+1)/N))/2) := by ring
    rw [he]
    exact (ht.trans (add_le_add hi hmid)).trans_eq (by ring)

end
end «2606.16671v2».SineJacobi
