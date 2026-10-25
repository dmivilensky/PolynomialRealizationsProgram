import chebyshev2.LocalObstruction.GroundSmooth
import chebyshev2.LocalObstruction.ScalarRootVariation

/-!
Article: chebyshev2, Theorem 6.1.
One-direction versions of the actual finite perturbation families.
Use: `chebyshev2.LocalObstruction.single_ground_root_near` feeds
`chebyshev2.LocalObstruction.groundCoupling_density_derivative` (ground Coupling density
derivative).
Proof chain: `chebyshev2.LocalObstruction.groundObservationWitness` — chebyshev2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open MeasureTheory Real Set Filter chebyshev2.Filters chebyshev2.GroundState
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 /--
Exact identity `perturb m (fun _ : Unit => v) (fun _ => ε)=m+ε • v`.

Use: `chebyshev2.LocalObstruction.groundCoupling_single_c1` rewrites with this identity to
establish smoothness to the stated order: `ContDiffAt ℝ 1 (fun ε : ℝ => groundCoupling (m+ε •
v)) 0`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem perturbUnit_eq (m v : ℝ → ℝ) (ε : ℝ) :
    perturb m (fun _ : Unit => v) (fun _ => ε)=m+ε • v := by
  funext x
  simp [perturb]

 /--
Defines `singleTransmission` of type `ℝ` by `signedTransmission (hm.add (hv.smul p.1)) p.2`.

Use: `chebyshev2.LocalObstruction.singleTransmission_analytic` uses this definition to
establish the precise assertion is `AnalyticAt ℝ (singleTransmission hm hv) p`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.
-/
def singleTransmission {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v) (p : ℝ × ℝ) : ℝ :=
  signedTransmission (hm.add (hv.smul p.1)) p.2

 /--
The precise assertion is `AnalyticAt ℝ (singleTransmission hm hv) p`.

Use: `chebyshev2.LocalObstruction.groundCoupling_density_derivative` uses this assertion to
establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => groundCoupling
(m+ε • v)) (-groundParameter hm (fun x => (hn x).le)*(∫ x,v x*(H1.rep G.u x)^2)/ (∫ x,m
x*(H1.rep G.u x)^2)) 0`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem singleTransmission_analytic {m v : ℝ → ℝ} (hm : Integrable m) (hv : Integrable v)
    (p : ℝ × ℝ) : AnalyticAt ℝ (singleTransmission hm hv) p := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hp : AnalyticAt ℝ (fun z : ℝ × ℝ => ((fun _ : Unit => z.1),z.2)) p :=
    (AnalyticAt.pi (fun _ : Unit => analyticAt_fst)).prod analyticAt_snd
  have h := (perturbTransmission_signed_analytic hm (fun _ : Unit => hv)
    ((fun _ : Unit => p.1),p.2)).comp (f := fun z : ℝ × ℝ => ((fun _ : Unit => z.1),z.2)) hp
  convert! h using 1
  funext z
  dsimp only [Function.comp_def]
  simp only [perturbTransmission_signed_actual,perturbUnit_eq]
  rfl

 /--
Smoothness to the stated order: `ContDiffAt ℝ 1 (fun ε : ℝ => groundCoupling (m+ε • v)) 0`.

Use: `chebyshev2.LocalObstruction.groundCoupling_density_derivative` uses this identity to
establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => groundCoupling
(m+ε • v)) (-groundParameter hm (fun x => (hn x).le)*(∫ x,v x*(H1.rep G.u x)^2)/ (∫ x,m
x*(H1.rep G.u x)^2)) 0`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem groundCoupling_single_c1 {m v : ℝ → ℝ} (hm : Integrable m) (hc : Continuous m)
    (hn : ∀ x,0<m x) (hM : Integrable (fun x => exp (-x)*m x)) (he : ∀ x,m (-x)=m x)
    (hv : Integrable v) (hvc : Continuous v) (hvcomp : HasCompactSupport v) :
    ContDiffAt ℝ 1 (fun ε : ℝ => groundCoupling (m+ε • v)) 0 := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have h := groundCoupling_finite_c1 hm hc hn hM he (fun _ : Unit => hv)
    (fun _ : Unit => hvc) (fun _ : Unit => hvcomp)
  have hp : ContDiffAt ℝ 1 (fun ε : ℝ => (fun _ : Unit => ε)) 0 := by fun_prop
  have h' : ContDiffAt ℝ 1 (fun a : Unit → ℝ => groundCoupling (perturb m (fun _ : Unit => v) a))
      (fun _ : Unit => (0:ℝ)) := h
  convert! h'.comp (0:ℝ) hp using 1
  funext ε
  dsimp only [Function.comp_def]
  rw [perturbUnit_eq]

 /--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ ε : ℝ in 𝓝
0,singleTransmission hm hv (ε,-groundCoupling (m+ε • v))=0`.

Use: `chebyshev2.LocalObstruction.groundCoupling_density_derivative` uses this identity to
establish the actual derivative at the stated point: `HasDerivAt (fun ε : ℝ => groundCoupling
(m+ε • v)) (-groundParameter hm (fun x => (hn x).le)*(∫ x,v x*(H1.rep G.u x)^2)/ (∫ x,m
x*(H1.rep G.u x)^2)) 0`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.groundObservationWitness`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem single_ground_root_near {m v : ℝ → ℝ} (hm : Integrable m) (hc : Continuous m)
    (hn : ∀ x,0<m x) (hM : Integrable (fun x => exp (-x)*m x))
    (hv : Integrable v) (hvc : Continuous v) (hvcomp : HasCompactSupport v) :
    ∀ᶠ ε : ℝ in 𝓝 0,singleTransmission hm hv (ε,-groundCoupling (m+ε • v))=0 := by
  -- Record the convergence hmap with its source filter and target limit before taking limits
  -- in the subsequent identities/bounds.
  have hmap : Tendsto (fun ε : ℝ => (fun _ : Unit => ε)) (𝓝 0) (𝓝 (0:Unit → ℝ)) := by
    convert! (show Continuous (fun ε : ℝ => (fun _ : Unit => ε)) by fun_prop).continuousAt.tendsto using 1
  filter_upwards [hmap.eventually (actual_ground_root_near hm hc hn hM (fun _ : Unit => hv)
    (fun _ : Unit => hvc) (fun _ : Unit => hvcomp))] with ε hε
  simp only [perturbTransmission_signed_actual,perturbUnit_eq] at hε
  exact hε

end
end chebyshev2.LocalObstruction
