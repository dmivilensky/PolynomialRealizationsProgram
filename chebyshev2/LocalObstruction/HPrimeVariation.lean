import chebyshev2.LocalObstruction.HVariation
import chebyshev2.LocalObstruction.GreenGradientVariation
import chebyshev2.LocalObstruction.MixedPartial

/-!
Article: chebyshev2, Theorem 6.1.
Lemma 26(i): the actual mixed density/scale derivative of H.
Use: `chebyshev2.LocalObstruction.singleHPrime_density_derivative` feeds
`chebyshev2.LocalObstruction.observationS_density_derivative` (observation S density
derivative).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter chebyshev2.Filters chebyshev2.Continuum
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
Defines `singleHJoint` of type `ℝ` by `singleH hm hv p.2 p.1`.

Use: `chebyshev2.LocalObstruction.singleHPrime` uses this definition in the displayed
construction of `singleHPrime`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def singleHJoint {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v) (p : ℝ × ℝ) : ℝ :=
  singleH hm hv p.2 p.1

 /--
Defines `singleHPrime` of type `ℝ` by `fderiv ℝ (singleHJoint hm hv) (ε,s) (0,1)`.

Use: `chebyshev2.LocalObstruction.singleHPrime_density_derivative` uses this definition to
establish the actual derivative at the stated point: `HasDerivAt (singleHPrime hm hv s) (∫
x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def singleHPrime {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v) (s ε : ℝ) : ℝ :=
  fderiv ℝ (singleHJoint hm hv) (ε,s) (0,1)

 /--
The precise assertion is `AnalyticAt ℝ (singleHJoint hm hv) (0,s)`.

Use: `chebyshev2.LocalObstruction.singleHPrime_density_derivative` uses this assertion to
establish the actual derivative at the stated point: `HasDerivAt (singleHPrime hm hv s) (∫
x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.perturbH_joint_analytic`
with the arguments shown in the proof.
-/
theorem singleH_joint_analytic {m v : ℝ → ℝ} (hm : Integrable m) (hc : Continuous m)
    (hn : ∀ x,0<m x) (hv : Integrable v) (hvc : Continuous v) (hvcomp : HasCompactSupport v)
    {s : ℝ} (hs : 0<s) : AnalyticAt ℝ (singleHJoint hm hv) (0,s) := by
  have hp : AnalyticAt ℝ (fun z : ℝ × ℝ => ((fun _ : Unit => z.1),z.2)) (0,s) :=
    (AnalyticAt.pi (fun _ : Unit => analyticAt_fst)).prod analyticAt_snd
  exact (perturbH_joint_analytic hm hc hn (fun _ : Unit => hv)
    (fun _ : Unit => hvc) (fun _ : Unit => hvcomp) hs).comp
    (f := fun z : ℝ × ℝ => ((fun _ : Unit => z.1),z.2)) hp

 /--
Exact identity `fderiv ℝ (singleHJoint hm hv) (0,s) (1,0)=s*(∫ x,greenKernel s m x x*v x)`.

Use: `chebyshev2.LocalObstruction.singleHPrime_density_derivative` uses this identity to
establish the actual derivative at the stated point: `HasDerivAt (singleHPrime hm hv s) (∫
x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.singleH_joint_analytic`,
`chebyshev2.LocalObstruction.singleH_density_derivative` with the arguments shown in the
proof.
-/
theorem singleH_partial_density {m v : ℝ → ℝ} (hm : Integrable m) (hc : Continuous m)
    (hn : ∀ x,0<m x) (hv : Integrable v) (hvc : Continuous v) (hvcomp : HasCompactSupport v)
    {s : ℝ} (hs : 0<s) (he : ∀ x,m (-x)=m x) :
    fderiv ℝ (singleHJoint hm hv) (0,s) (1,0)=s*(∫ x,greenKernel s m x x*v x) := by
  -- Use the identities/estimates `chebyshev2.LocalObstruction.singleH_joint_analytic`,
  -- `chebyshev2.LocalObstruction.singleH_density_derivative` with the arguments shown in
  -- the proof.
  have hd := (singleH_joint_analytic hm hc hn hv hvc hvcomp hs).differentiableAt.hasFDerivAt
  have ht := hd.comp_hasDerivAt (0:ℝ)
    ((hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) s))
  have ht' : HasDerivAt (singleH hm hv s) (fderiv ℝ (singleHJoint hm hv) (0,s) (1,0)) 0 := by
    convert! ht using 1
  exact ht'.unique (singleH_density_derivative hm hc hn hv hvc hvcomp hs he)

 /--
The actual derivative at the stated point: `HasDerivAt (singleHPrime hm hv s) (∫ x,(greenKernel
s m x x+s*greenScaleGradient s m x)*v x) 0`.

Use: `chebyshev2.LocalObstruction.observationS_density_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ =>
observationS (m+ε • v) s) (∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem singleHPrime_density_derivative {m v : ℝ → ℝ} (hm : Integrable m) (hc : Continuous m)
    (hn : ∀ x,0<m x) (hv : Integrable v) (hvc : Continuous v) (hvcomp : HasCompactSupport v)
    {s : ℝ} (hs : 0<s) (he : ∀ x,m (-x)=m x) :
    HasDerivAt (singleHPrime hm hv s)
      (∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) 0 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hmixed := mixed_partial_derivative
    ((singleH_joint_analytic hm hc hn hv hvc hvcomp hs).contDiffAt (n := 2))
  have heq : (fun t : ℝ => fderiv ℝ (singleHJoint hm hv) (0,t) (1,0)) =ᶠ[𝓝 s]
      (fun t : ℝ => t*(∫ x,greenKernel t m x x*v x)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact singleH_partial_density hm hc hn hv hvc hvcomp ht he
  rw [heq.deriv_eq,(green_density_gradient_scale_derivative hm (fun x => (hn x).le) hc hs he hv).deriv] at hmixed
  exact hmixed

end
end chebyshev2.LocalObstruction
