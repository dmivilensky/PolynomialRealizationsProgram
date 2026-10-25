import chebyshev2.LocalObstruction.SineDecay
import chebyshev1.SineJacobi.ProfileHigherDerivatives
import Mathlib.Analysis.ODE.PicardLindelof

/-!
Article: chebyshev2, Theorem 6.1.
Smoothness of the actual sine density, using chebyshev1's profile regularity and the proved
inverse-coordinate ODE.
Use: `chebyshev2.SineContinuum.m_smooth` feeds
`chebyshev2.LocalObstruction.curveDensity_increment` (curve Density increment).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.SineContinuum
noncomputable section
open Set Real
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

 /--
Smoothness to the stated order: `ContDiffOn ℝ ∞ chebyshev2.SineJacobi.phi (Ioo (0:ℝ) 1)`.

Use: `chebyshev2.SineContinuum.T_smooth` uses this assertion to establish smoothness to the
stated order: `ContDiff ℝ ∞ T`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev1.SineJacobi.sineProfile_contDiffOn` with the
arguments shown in the proof.
-/
theorem phi_smooth : ContDiffOn ℝ ∞ chebyshev2.SineJacobi.phi (Ioo (0:ℝ) 1) := by
  have hs : ContDiffOn ℝ ∞ chebyshev1.SineJacobi.sineProfile (Ioo (0:ℝ) 1) :=
    contDiffOn_infty.mpr chebyshev1.SineJacobi.sineProfile_contDiffOn
  have hr := hs.comp (by fun_prop : ContDiffOn ℝ ∞ (fun t : ℝ => 1-t) (Ioo 0 1))
    (fun _ ht => ⟨by linarith [ht.2],by linarith [ht.1]⟩)
  exact contDiffOn_const.mul (hs.mul hr)

 /--
Smoothness to the stated order: `ContDiff ℝ ∞ T`.

Use: `chebyshev2.SineContinuum.n_smooth` uses this assertion to establish smoothness to the
stated order: `ContDiff ℝ ∞ n`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.phi_smooth`,
`chebyshev2.SineContinuum.T_derivative`, `chebyshev2.SineContinuum.T_mem` with the
arguments shown in the proof.
-/
theorem T_smooth : ContDiff ℝ ∞ T := by
  -- Use the identities/estimates `chebyshev2.SineContinuum.phi_smooth`,
  -- `chebyshev2.SineContinuum.T_derivative`, `chebyshev2.SineContinuum.T_mem` with the
  -- arguments shown in the proof.
  rw [contDiff_iff_contDiffAt]
  intro x
  have hF : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => chebyshev2.SineJacobi.phi p.2)
      (Icc (x-1) (x+1) ×ˢ Ioo (0:ℝ) 1) :=
    phi_smooth.comp contDiffOn_snd (fun _ hp => hp.2)
  have h := ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
    (f := fun _ y => chebyshev2.SineJacobi.phi y) hF
    (fun t _ => (T_derivative t).hasDerivWithinAt) (fun t _ => T_mem t)
  exact h.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))

 /--
Smoothness to the stated order: `ContDiff ℝ ∞ n`.

Use: `chebyshev2.SineContinuum.m_smooth` uses this assertion to establish smoothness to the
stated order: `ContDiff ℝ ∞ m`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.phi_smooth`,
`chebyshev2.SineContinuum.T_mem`, `chebyshev2.SineContinuum.T_smooth` with the
arguments shown in the proof.
-/
theorem n_smooth : ContDiff ℝ ∞ n := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (phi_smooth.contDiffAt (Ioo_mem_nhds (T_mem x).1 (T_mem x).2)).comp x
    T_smooth.contDiffAt

 /--
Smoothness to the stated order: `ContDiff ℝ ∞ m`.

Use: `chebyshev2.LocalObstruction.curveDensity_increment` uses this assertion to establish
smoothness to the stated order: `ContDiff ℝ ∞ (fun x => curveDensity h w t x-m x) ∧
HasCompactSupport (fun x => curveDensity h w t x-m x)`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.SineContinuum.n_smooth` with the arguments
shown in the proof.
-/
theorem m_smooth : ContDiff ℝ ∞ m := n_smooth.pow 2

end
end chebyshev2.SineContinuum
