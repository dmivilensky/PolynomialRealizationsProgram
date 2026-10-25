import chebyshev2.LocalObstruction.HPrimeVariation
import chebyshev2.LocalObstruction.ParameterDerivative
import chebyshev2.LocalObstruction.SingleFamilies

/-!
Article: chebyshev2, Theorem 6.1.
The observations are the literal Fredholm/Jost logarithm and its classical scale derivative.
Use: `chebyshev2.LocalObstruction.observationS_density_derivative` feeds
`chebyshev2.LocalObstruction.theorem_6_1` (theorem 6 1).
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
Defines `observationH` of type `ℝ` by `log (transmission s m)`.

Use: `chebyshev2.LocalObstruction.observationH_single_eq` uses this definition to establish
the stated quantitative bound `(fun p : ℝ × ℝ => observationH (m+p.1 • v) p.2) =ᶠ[𝓝 (0,s)]
singleHJoint hm hv`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.observationH_finite_joint_analytic`.
-/
def observationH (m : ℝ → ℝ) (s : ℝ) : ℝ := log (transmission s m)
 /--
Defines `observationS` of type `ℝ` by `deriv (observationH m) s`.

Use: `chebyshev2.LocalObstruction.observationS_actual` uses this definition to establish
exact identity `observationS m s=deriv (logDeterminant (kernelEigenvalue hm hn)) s`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.observationS_finite_joint_c1`.
-/
def observationS (m : ℝ → ℝ) (s : ℝ) : ℝ := deriv (observationH m) s

 /--
Exact identity `observationH m s=logDeterminant (kernelEigenvalue hm hn) s`.

Use: `chebyshev2.LocalObstruction.observationH_finite_joint_analytic` rewrites with this
identity to prove the bound `AnalyticAt ℝ (fun p : (ι → ℝ) × ℝ =>
observationH (perturb m v p.1) p.2) (0,s)`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.observationH_finite_joint_analytic`.

Proof: Use the identities/estimates `chebyshev2.Filters.log_transmission_eq_logDeterminant`
with the arguments shown in the proof.
-/
theorem observationH_actual {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    {s : ℝ} (hs : 0≤s) : observationH m s=logDeterminant (kernelEigenvalue hm hn) s :=
  log_transmission_eq_logDeterminant hm hn hs

 /--
Exact identity `observationS m s=deriv (logDeterminant (kernelEigenvalue hm hn)) s`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 6.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem observationS_actual {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x)
    {s : ℝ} (hs : 0<s) : observationS m s=deriv (logDeterminant (kernelEigenvalue hm hn)) s := by
  unfold observationS
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hs] with t ht
  exact observationH_actual hm hn ht.le

 /--
The stated quantitative bound `AnalyticAt ℝ (fun p : (ι → ℝ) × ℝ => observationH (perturb m v
p.1) p.2) (0,s)`.

Use: `chebyshev2.LocalObstruction.observationS_finite_joint_c1` uses this identity to
establish smoothness to the stated order: `ContDiffAt ℝ 1 (fun p : (ι → ℝ) × ℝ => observationS
(perturb m v p.1) p.2) (0,s)`.

Article: chebyshev2, Theorem 6.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem observationH_finite_joint_analytic {ι : Type*} [Fintype ι]
    {m : ℝ → ℝ} {v : ι → ℝ → ℝ} (hm : Integrable m) (hc : Continuous m) (hn : ∀ x,0<m x)
    (hv : ∀ i,Integrable (v i)) (hvc : ∀ i,Continuous (v i)) (hcomp : ∀ i,HasCompactSupport (v i))
    {s : ℝ} (hs : 0<s) :
    AnalyticAt ℝ (fun p : (ι → ℝ) × ℝ => observationH (perturb m v p.1) p.2) (0,s) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply (perturbH_joint_analytic hm hc hn hv hvc hcomp hs).congr
  have hpos := (continuous_fst.tendsto ((0:ι → ℝ),s)).eventually
    (finite_perturbation_positive hc hn hvc hcomp)
  have hspos := (continuous_snd.tendsto ((0:ι → ℝ),s)).eventually (Ioi_mem_nhds hs)
  filter_upwards [hpos,hspos] with p hp hsp
  rw [perturbH_actual hm hv p (fun x => (hp x).le),
    observationH_actual (perturb_integrable hm hv p.1) (fun x => (hp x).le) hsp.le]

 /--
Smoothness to the stated order: `ContDiffAt ℝ 1 (fun p : (ι → ℝ) × ℝ => observationS (perturb m
v p.1) p.2) (0,s)`.

Use: `chebyshev2.LocalObstruction.sObservationWitness` uses this identity in the displayed
construction of `sObservationWitness`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 6.1.

Proof: Use the identities/estimates `chebyshev2.LocalObstruction.parameter_derivative_c1`,
`chebyshev2.LocalObstruction.observationH_finite_joint_analytic` with the arguments shown
in the proof.
-/
theorem observationS_finite_joint_c1 {ι : Type*} [Fintype ι]
    {m : ℝ → ℝ} {v : ι → ℝ → ℝ} (hm : Integrable m) (hc : Continuous m) (hn : ∀ x,0<m x)
    (hv : ∀ i,Integrable (v i)) (hvc : ∀ i,Continuous (v i)) (hcomp : ∀ i,HasCompactSupport (v i))
    {s : ℝ} (hs : 0<s) :
    ContDiffAt ℝ 1 (fun p : (ι → ℝ) × ℝ => observationS (perturb m v p.1) p.2) (0,s) :=
  parameter_derivative_c1 (observationH_finite_joint_analytic hm hc hn hv hvc hcomp hs).contDiffAt

 /--
The stated quantitative bound `(fun p : ℝ × ℝ => observationH (m+p.1 • v) p.2) =ᶠ[𝓝 (0,s)]
singleHJoint hm hv`.

Use: `chebyshev2.LocalObstruction.observationH_density_derivative` uses this identity to
establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => observationH
(m+ε • v) s) (s*(∫ x,greenKernel s m x x*v x)) 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem observationH_single_eq {m v : ℝ → ℝ} (hm : Integrable m) (hc : Continuous m)
    (hn : ∀ x,0<m x) (hv : Integrable v) (hvc : Continuous v) (hvcomp : HasCompactSupport v)
    {s : ℝ} (hs : 0<s) :
    (fun p : ℝ × ℝ => observationH (m+p.1 • v) p.2) =ᶠ[𝓝 (0,s)] singleHJoint hm hv := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hpos := (continuous_fst.tendsto ((0:ℝ),s)).eventually
    ((show Continuous (fun ε : ℝ => (fun _ : Unit => ε)) by fun_prop).continuousAt.tendsto.eventually
      (finite_perturbation_positive hc hn (fun _ : Unit => hvc) (fun _ : Unit => hvcomp)))
  have hspos := (continuous_snd.tendsto ((0:ℝ),s)).eventually (Ioi_mem_nhds hs)
  filter_upwards [hpos,hspos] with p hp hsp
  change observationH (m+p.1 • v) p.2=perturbH hm (fun _ : Unit => hv) ((fun _ => p.1),p.2)
  rw [perturbH_actual hm (fun _ : Unit => hv) _ (fun x => (hp x).le),
    ← log_transmission_eq_logDeterminant (perturb_integrable hm (fun _ : Unit => hv) (fun _ => p.1))
      (fun x => (hp x).le) hsp.le]
  simp only [perturbUnit_eq]
  rfl

 /--
The actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => observationH (m+ε • v) s)
(s*(∫ x,greenKernel s m x x*v x)) 0`.

Use: `chebyshev2.LocalObstruction.hObservationWitness` uses this derivative formula in the
displayed construction of `hObservationWitness`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates
`chebyshev2.LocalObstruction.singleH_density_derivative`,
`chebyshev2.LocalObstruction.observationH_single_eq` with the arguments shown in the proof.
-/
theorem observationH_density_derivative {m v : ℝ → ℝ} (hm : Integrable m) (hc : Continuous m)
    (hn : ∀ x,0<m x) (hv : Integrable v) (hvc : Continuous v) (hvcomp : HasCompactSupport v)
    {s : ℝ} (hs : 0<s) (he : ∀ x,m (-x)=m x) :
    HasDerivAt (fun ε : ℝ => observationH (m+ε • v) s) (s*(∫ x,greenKernel s m x x*v x)) 0 := by
  apply (singleH_density_derivative hm hc hn hv hvc hvcomp hs he).congr_of_eventuallyEq
  have hmap : Tendsto (fun ε : ℝ => (ε,s)) (𝓝 0) (𝓝 (0,s)) :=
    continuousAt_id.tendsto.prodMk_nhds continuousAt_const.tendsto
  exact hmap.eventually (observationH_single_eq hm hc hn hv hvc hvcomp hs)

 /--
The actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => observationS (m+ε • v) s)
(∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) 0`.

Use: `chebyshev2.LocalObstruction.sObservationWitness` uses this derivative formula in the
displayed construction of `sObservationWitness`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem observationS_density_derivative {m v : ℝ → ℝ} (hm : Integrable m) (hc : Continuous m)
    (hn : ∀ x,0<m x) (hv : Integrable v) (hvc : Continuous v) (hvcomp : HasCompactSupport v)
    {s : ℝ} (hs : 0<s) (he : ∀ x,m (-x)=m x) :
    HasDerivAt (fun ε : ℝ => observationS (m+ε • v) s)
      (∫ x,(greenKernel s m x x+s*greenScaleGradient s m x)*v x) 0 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply (singleHPrime_density_derivative hm hc hn hv hvc hvcomp hs he).congr_of_eventuallyEq
  have hF : ContDiffAt ℝ 2 (singleHJoint hm hv) (0,s) :=
    (singleH_joint_analytic hm hc hn hv hvc hvcomp hs).contDiffAt
  -- Record the convergence hmap with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hmap : Tendsto (fun ε : ℝ => (ε,s)) (𝓝 0) (𝓝 (0,s)) :=
    continuousAt_id.tendsto.prodMk_nhds continuousAt_const.tendsto
  filter_upwards [hmap.eventually (hF.eventually (by norm_num : (2:ℕ∞ω)≠∞)),
    hmap.eventually (observationH_single_eq hm hc hn hv hvc hvcomp hs).eventuallyEq_nhds] with ε hε heq
  change deriv (fun t : ℝ => observationH (m+ε • v) t) s=
    fderiv ℝ (singleHJoint hm hv) (ε,s) (0,1)
  have ht : (fun t : ℝ => observationH (m+ε • v) t)=ᶠ[𝓝 s]
      (fun t : ℝ => singleHJoint hm hv (ε,t)) :=
    (continuousAt_const.tendsto.prodMk_nhds continuousAt_id.tendsto).eventually heq
  rw [ht.deriv_eq,parameter_derivative_eq (hε.differentiableAt (by norm_num : (2:ℕ∞ω)≠0))]

end
end chebyshev2.LocalObstruction
