import «2610.05164v2».LocalObstruction.TransmissionVariation
import «2610.05164v2».LocalObstruction.GreenIdentities

/-!
Article: 2610.05164v2, Theorem 6.1.
Lemma 26(i): density differentiation of the actual Fredholm logarithm.
Use: `«2610.05164v2».LocalObstruction.singleH_density_derivative` feeds
`«2610.05164v2».LocalObstruction.observationH_density_derivative` (observation H density
derivative).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Filters «2610.05164v2».HalfLine «2610.05164v2».Continuum
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
Defines `singleH` of type `ℝ` by `perturbH hm (fun _ : Unit => hv) ((fun _ => ε),s)`.

Use: `«2610.05164v2».LocalObstruction.singleH_density_derivative` rewrites with this definition
to establish the actual derivative at the stated point: `HasDerivAt (singleH hm hv s) (s*(∫
x,greenKernel s m x x*v x)) 0`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.
-/
def singleH {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v) (s ε : ℝ) : ℝ :=
  perturbH hm (fun _ : Unit => hv) ((fun _ => ε),s)

 /--
The actual derivative at the stated point: `HasDerivAt (singleH hm hv s) (s*(∫ x,greenKernel s
m x x*v x)) 0`.

Use: `«2610.05164v2».LocalObstruction.observationH_density_derivative` uses this derivative
formula to establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ =>
observationH (m+ε • v) s) (s*(∫ x,greenKernel s m x x*v x)) 0`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Identify the summands/integrands on their required
domain before replacing the sum or integral. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem singleH_density_derivative {m v : ℝ → ℝ} (hm : Integrable m) (hc : Continuous m)
    (hn : ∀ x,0<m x) (hv : Integrable v) (hvc : Continuous v) (hvcomp : HasCompactSupport v)
    {s : ℝ} (hs : 0<s) (he : ∀ x,m (-x)=m x) :
    HasDerivAt (singleH hm hv s) (s*(∫ x,greenKernel s m x x*v x)) 0 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hnp := fun x => (hn x).le
  have hT : 0<signedTransmission (hm.add (hv.smul (0:ℝ))) s := by
    have hz : signedTransmission (hm.add (hv.smul (0:ℝ))) s=signedTransmission hm s := by
      congr 1
      simp
    rw [hz,signedTransmission_actual hm hnp hs.le]
    exact zero_lt_one.trans_le (transmission_ge_one hm hnp hs.le)
  have hd := (signedTransmission_density_derivative hm hv s he).log hT.ne'
  have hz : signedTransmission (hm.add (hv.smul (0:ℝ))) s=transmission s m := by
    have hz' : m+(0:ℝ) • v=m := by simp
    simpa only [hz'] using (signedTransmission_actual hm hnp hs.le)
  have hj (x : ℝ) : signedJost hm s x=jost s m x :=
    congrArg (fun f : VolterraSpace => f x) (signedJost_actual hm hnp hs.le)
  have hgrad : (∫ x,greenKernel s m x x*v x)=
      (∫ x,v x*jost s m x*jost s m (-x))/(2*transmission s m) := by
    rw [← integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      dsimp only
      rw [greenKernel_diagonal_jost hm hnp hc hs.le he]
      ring)
  have hederiv : (s/2*(∫ x,v x*signedJost hm s x*signedJost hm s (-x)))/
      signedTransmission (hm.add (hv.smul (0:ℝ))) s=s*(∫ x,greenKernel s m x x*v x) := by
    simp_rw [hj]
    rw [hz,hgrad]
    ring
  rw [hederiv] at hd
  apply hd.congr_of_eventuallyEq
  -- Record the convergence hmap with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hmap : Tendsto (fun ε : ℝ => (fun _ : Unit => ε)) (𝓝 0) (𝓝 (0:Unit → ℝ)) := by
    convert! (show Continuous (fun ε : ℝ => (fun _ : Unit => ε)) by fun_prop).continuousAt.tendsto using 1
  have hpos := hmap.eventually
    (finite_perturbation_positive hc hn (fun _ : Unit => hvc) (fun _ : Unit => hvcomp))
  filter_upwards [hpos] with ε hp
  have hfun : perturb m (fun _ : Unit => v) (fun _ => ε)=m+ε • v := by
    funext x
    simp [perturb]
  have hn' : ∀ x,0≤(m+ε • v) x := fun x => by rw [← hfun];exact (hp x).le
  change singleH hm hv s ε=log (signedTransmission (hm.add (hv.smul ε)) s)
  rw [singleH,perturbH_actual hm (fun _ : Unit => hv) _ (fun x => (hp x).le),
    ← log_transmission_eq_logDeterminant
      (perturb_integrable hm (fun _ : Unit => hv) (fun _ => ε)) (fun x => (hp x).le) hs.le,
    signedTransmission_actual (hm.add (hv.smul ε)) hn' hs.le,hfun]

end
end «2610.05164v2».LocalObstruction
