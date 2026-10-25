import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
Article: chebyshev2, Theorem 6.1.
A scalar implicit-function theorem identifies any continuous actual root with the C1 local branch;
no choice of a surrogate root remains in the result.
Use: `chebyshev2.LocalObstruction.contDiffAt_scalar_root` feeds
`chebyshev2.LocalObstruction.groundCoupling_finite_c1` (ground Coupling finite c1).
Proof chain: `chebyshev2.LocalObstruction.groundObservationWitness` — chebyshev2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Filter
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 /--
Smoothness to the stated order: `ContDiffAt ℝ 1 g a`.

Use: `chebyshev2.LocalObstruction.groundCoupling_finite_c1` uses this assertion to
establish smoothness to the stated order: `ContDiffAt ℝ 1 (fun a : ι → ℝ => groundCoupling
(perturb m v a)) 0`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem contDiffAt_scalar_root {F : E × ℝ → ℝ} {g : E → ℝ} {a : E} {c : ℝ}
    (hF : ContDiffAt ℝ 1 F (a,g a)) (hg : ContinuousAt g a)
    (hzero : ∀ᶠ x in 𝓝 a,F (x,g x)=F (a,g a))
    (hd : HasDerivAt (fun t : ℝ => F (a,t)) c (g a)) (hc : c≠0) :
    ContDiffAt ℝ 1 g a := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let D := fderiv ℝ F (a,g a) ∘L ContinuousLinearMap.inr ℝ E ℝ
  have hdf := hF.differentiableAt (by norm_num : (1:ℕ∞ω)≠0) |>.hasFDerivAt
  have ht := hdf.comp_hasDerivAt (g a)
    ((hasDerivAt_const (g a) a).prodMk (hasDerivAt_id (g a)))
  have ht' : HasDerivAt (fun t : ℝ => F (a,t)) (D 1) (g a) := by
    convert! ht using 1
  have hD1 : D 1=c := ht'.unique hd
  have he : (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc) : ℝ →L[ℝ] ℝ)=D := by
    apply ContinuousLinearMap.ext
    intro t
    have hh := D.map_smul t (1:ℝ)
    simpa only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.unitsEquivAut_apply,Units.val_mk0,
      smul_eq_mul,mul_one,hD1,mul_comm] using hh.symm
  have hInv : D.IsInvertible := ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 c hc),he⟩
  let b := hF.implicitFunction (by norm_num : (1:ℕ∞ω)≠0) hInv
  have hb : ContDiffAt ℝ 1 b a := hF.contDiffAt_implicitFunction _ hInv
  have hi := hF.eventually_apply_eq_iff_implicitFunction (by norm_num : (1:ℕ∞ω)≠0) hInv
  -- Record the convergence hmap with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hmap : Tendsto (fun x => (x,g x)) (𝓝 a) (𝓝 (a,g a)) :=
    continuousAt_id.tendsto.prodMk_nhds hg.tendsto
  apply hb.congr_of_eventuallyEq
  filter_upwards [hmap.eventually hi,hzero] with x hx hz
  exact (hx.mp hz).symm

end
end chebyshev2.LocalObstruction
