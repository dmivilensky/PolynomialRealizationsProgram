import «2610.05164v2».Calibration.CubicRoot
import «2610.05164v2».Calculus.ImplicitScalar
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
Article: 2610.05164v2, Lemma 19.
Nonsingularity and smoothness of the actual positive cubic root.
Use: `«2610.05164v2».Calibration.positiveRoot_contDiffOn` feeds
`«2610.05164v2».Numerics.positiveCubic_smooth` (positive Cubic smooth).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_stable` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Calibration
noncomputable section
open Set Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `0 < 3*κ*(positiveRoot κ Q c)^2-3*Q`.

Use: `«2610.05164v2».Calibration.positiveRoot_contDiffOn` uses this bound to establish
smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × ℝ => positiveRoot p.1 p.2.1
p.2.2) {p | 0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2}`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.positiveRoot_spec` with the
arguments shown in the proof.
-/
theorem positiveRoot_nonsingular {κ Q c : ℝ}
    (hκ : 0 < κ) (hQ : 0 ≤ Q) (hc : 0 < c) :
    0 < 3*κ*(positiveRoot κ Q c)^2-3*Q := by
  obtain ⟨hv,he⟩ := positiveRoot_spec hκ hQ hc
  dsimp only [cubic] at he
  have hi : κ*(positiveRoot κ Q c)^2>3*Q := by
    nlinarith [mul_pos hv hc]
  linarith

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × ℝ => positiveRoot p.1 p.2.1
p.2.2) {p | 0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2}`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedRoot_smooth` uses this identity to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ R.normalizedRoot (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem E.1 via `«2610.05164v2».DualCertificate.Data.admissible_stable`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem positiveRoot_contDiffOn : ContDiffOn ℝ ∞
    (fun p : ℝ × ℝ × ℝ => positiveRoot p.1 p.2.1 p.2.2)
    {p | 0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2} := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  intro p hp
  let f : (ℝ × ℝ × ℝ) × ℝ → ℝ := fun z => cubic z.1.1 z.1.2.1 z.1.2.2 z.2
  have hf : ContDiff ℝ ∞ f := by unfold f cubic; fun_prop
  have hd : HasDerivAt (fun v => f (p,v))
      (3*p.1*(positiveRoot p.1 p.2.1 p.2.2)^2-3*p.2.1)
      (positiveRoot p.1 p.2.1 p.2.2) := by
    convert! ((((hasDerivAt_id (positiveRoot p.1 p.2.1 p.2.2)).pow 3).const_mul p.1).sub
      ((hasDerivAt_id (positiveRoot p.1 p.2.1 p.2.2)).const_mul (3*p.2.1))).sub_const p.2.2 using 1
    dsimp [f,cubic]
    ring
  apply «2610.05164v2».Calculus.implicit_contDiffWithinAt hf.contDiffAt (by simp)
    (positiveRoot_continuousOn p hp)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (positiveRoot_spec hy.1 hy.2.1 hy.2.2).2.trans
      (positiveRoot_spec hp.1 hp.2.1 hp.2.2).2.symm
  · exact «2610.05164v2».Calculus.scalar_derivative_invertible
      (hf.differentiable (by norm_num) _) hd
      (positiveRoot_nonsingular hp.1 hp.2.1 hp.2.2).ne'

end
end «2610.05164v2».Calibration
