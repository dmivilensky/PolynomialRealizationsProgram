import «2610.05164v2».LocalObstruction.SineDecay
import «2606.16671v2».SineJacobi.ProfileHigherDerivatives
import Mathlib.Analysis.ODE.PicardLindelof

/-!
Article: 2610.05164v2, Theorem 6.1.
Smoothness of the actual sine density, using 2606.16671v2's profile regularity and the proved
inverse-coordinate ODE.
Use: `«2610.05164v2».SineContinuum.m_smooth` feeds
`«2610.05164v2».LocalObstruction.curveDensity_increment` (curve Density increment).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Set Real
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

 /--
Smoothness to the stated order: `ContDiffOn ℝ ∞ «2610.05164v2».SineJacobi.phi (Ioo (0:ℝ) 1)`.

Use: `«2610.05164v2».SineContinuum.T_smooth` uses this assertion to establish smoothness to the
stated order: `ContDiff ℝ ∞ T`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.sineProfile_contDiffOn` with the
arguments shown in the proof.
-/
theorem phi_smooth : ContDiffOn ℝ ∞ «2610.05164v2».SineJacobi.phi (Ioo (0:ℝ) 1) := by
  have hs : ContDiffOn ℝ ∞ «2606.16671v2».SineJacobi.sineProfile (Ioo (0:ℝ) 1) :=
    contDiffOn_infty.mpr «2606.16671v2».SineJacobi.sineProfile_contDiffOn
  have hr := hs.comp (by fun_prop : ContDiffOn ℝ ∞ (fun t : ℝ => 1-t) (Ioo 0 1))
    (fun _ ht => ⟨by linarith [ht.2],by linarith [ht.1]⟩)
  exact contDiffOn_const.mul (hs.mul hr)

 /--
Smoothness to the stated order: `ContDiff ℝ ∞ T`.

Use: `«2610.05164v2».SineContinuum.n_smooth` uses this assertion to establish smoothness to the
stated order: `ContDiff ℝ ∞ n`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.phi_smooth`,
`«2610.05164v2».SineContinuum.T_derivative`, `«2610.05164v2».SineContinuum.T_mem` with the
arguments shown in the proof.
-/
theorem T_smooth : ContDiff ℝ ∞ T := by
  -- Use the identities/estimates `«2610.05164v2».SineContinuum.phi_smooth`,
  -- `«2610.05164v2».SineContinuum.T_derivative`, `«2610.05164v2».SineContinuum.T_mem` with the
  -- arguments shown in the proof.
  rw [contDiff_iff_contDiffAt]
  intro x
  have hF : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => «2610.05164v2».SineJacobi.phi p.2)
      (Icc (x-1) (x+1) ×ˢ Ioo (0:ℝ) 1) :=
    phi_smooth.comp contDiffOn_snd (fun _ hp => hp.2)
  have h := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
    (f := fun _ y => «2610.05164v2».SineJacobi.phi y) hF
    (fun t _ => (T_derivative t).hasDerivWithinAt) (fun t _ => T_mem t)
  exact h.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))

 /--
Smoothness to the stated order: `ContDiff ℝ ∞ n`.

Use: `«2610.05164v2».SineContinuum.m_smooth` uses this assertion to establish smoothness to the
stated order: `ContDiff ℝ ∞ m`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.phi_smooth`,
`«2610.05164v2».SineContinuum.T_mem`, `«2610.05164v2».SineContinuum.T_smooth` with the
arguments shown in the proof.
-/
theorem n_smooth : ContDiff ℝ ∞ n := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (phi_smooth.contDiffAt (Ioo_mem_nhds (T_mem x).1 (T_mem x).2)).comp x
    T_smooth.contDiffAt

 /--
Smoothness to the stated order: `ContDiff ℝ ∞ m`.

Use: `«2610.05164v2».LocalObstruction.curveDensity_increment` uses this assertion to establish
smoothness to the stated order: `ContDiff ℝ ∞ (fun x => curveDensity h w t x-m x) ∧
HasCompactSupport (fun x => curveDensity h w t x-m x)`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.n_smooth` with the arguments
shown in the proof.
-/
theorem m_smooth : ContDiff ℝ ∞ m := n_smooth.pow 2

end
end «2610.05164v2».SineContinuum
