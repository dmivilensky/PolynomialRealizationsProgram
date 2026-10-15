import «2610.05164v2».LocalObstruction.VolterraAnalytic
import «2610.05164v2».Filters.FredholmJost
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
Article: 2610.05164v2, Theorem 6.1.
Lemma 26(i): real analyticity of the actual Fredholm logarithm under finite smooth compact density
perturbations, obtained from Jost transmission.
Use: `«2610.05164v2».LocalObstruction.perturbH_joint_analytic` feeds
`«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic` (observation H finite joint
analytic).
Proof chain: `«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic` — 2610.05164v2,
Theorem 6.1; No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Filters «2610.05164v2».Continuum
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
Exact identity `volterraMass (perturb_integrable hm hv a) f=volterraMass hm f+∑ i,a
i*volterraMass (hv i) f`.

Use: `«2610.05164v2».LocalObstruction.perturbTransmission_actual` rewrites with this identity
to establish the identity `perturbTransmission hm hv p=transmission p.2 (perturb m v p.1)`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem volterraMass_perturb {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (a : ι → ℝ) (f : VolterraSpace) :
    volterraMass (perturb_integrable hm hv a) f=volterraMass hm f+∑ i,a i*volterraMass (hv i) f := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hbase := bounded_forcing_integrable hm f.continuous.aestronglyMeasurable f.norm_coe_le_norm
  have hdir (i : ι) := bounded_forcing_integrable (hv i) f.continuous.aestronglyMeasurable f.norm_coe_le_norm
  simp only [volterraMass_apply]
  have he : (fun x => perturb m v a x*f x)=fun x => m x*f x+∑ i,a i*(v i x*f x) := by
    funext x
    unfold perturb
    rw [add_mul,Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,integral_add hbase (integrable_finsetSum _ (fun i _ => (hdir i).const_mul (a i))),
    integral_finsetSum _ (fun i _ => (hdir i).const_mul (a i))]
  simp only [integral_const_mul]

 /--
Defines `perturbTransmission` of type `ℝ` by `1+p.2/2*(volterraMass hm (volterraSolution hm hv
p)+ ∑ i,p.1 i*volterraMass (hv i) (volterraSolution hm hv p))`.

Use: `«2610.05164v2».LocalObstruction.perturbH_joint_analytic` uses this definition to
establish the precise assertion is `AnalyticAt ℝ (perturbH hm hv) ((0:ι → ℝ),s)`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.
-/
def perturbTransmission {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (p : (ι → ℝ) × ℝ) : ℝ :=
  1+p.2/2*(volterraMass hm (volterraSolution hm hv p)+
    ∑ i,p.1 i*volterraMass (hv i) (volterraSolution hm hv p))

 /--
Exact identity `perturbTransmission hm hv p=transmission p.2 (perturb m v p.1)`.

Use: `«2610.05164v2».LocalObstruction.perturbH_joint_analytic` rewrites with this identity to
establish the precise assertion is `AnalyticAt ℝ (perturbH hm hv) ((0:ι → ℝ),s)`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Proof: Use the identities/estimates `«2610.05164v2».LocalObstruction.volterraMass_perturb`,
`«2610.05164v2».LocalObstruction.volterraSolution_actual` with the arguments shown in the
proof.
-/
theorem perturbTransmission_actual {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (p : (ι → ℝ) × ℝ)
    (hn : ∀ x,0≤perturb m v p.1 x) (hs : 0≤p.2) :
    perturbTransmission hm hv p=transmission p.2 (perturb m v p.1) := by
  unfold perturbTransmission
  rw [← volterraMass_perturb hm hv p.1,volterraSolution_actual hm hv p hn hs]
  rfl

 /--
The precise assertion is `AnalyticAt ℝ (perturbTransmission hm hv) ((0:ι → ℝ),s)`.

Use: `«2610.05164v2».LocalObstruction.perturbH_joint_analytic` uses this assertion to establish
the precise assertion is `AnalyticAt ℝ (perturbH hm hv) ((0:ι → ℝ),s)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem perturbTransmission_joint_analytic {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hn : ∀ x,0≤m x) (hv : ∀ i,Integrable (v i)) {s : ℝ} (hs : 0≤s) :
    AnalyticAt ℝ (perturbTransmission hm hv) ((0:ι → ℝ),s) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hsol := volterraSolution_joint_analytic hm hn hv hs
  apply analyticAt_const.add
  apply (analyticAt_snd.div_const (c := (2:ℝ))).mul
  apply ((volterraMass hm).analyticAt _ |>.comp (f := volterraSolution hm hv) hsol).add
  have hsum := Finset.analyticAt_sum Finset.univ (f := fun i (p : (ι → ℝ) × ℝ) =>
    p.1 i*volterraMass (hv i) (volterraSolution hm hv p)) (fun i _ =>
      (((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).analyticAt (0:ι → ℝ)).comp (f := fun p : (ι → ℝ) × ℝ => p.1) analyticAt_fst).mul
        (((volterraMass (hv i)).analyticAt _).comp (f := volterraSolution hm hv) hsol))
  convert! hsum using 1
  funext p
  simp only [Finset.sum_apply]

 /--
Constructs the object of type `ℝ` and discharges its required properties in the accompanying
proof.

Use: `«2610.05164v2».LocalObstruction.perturbH_actual` rewrites with this definition to
establish exact identity `perturbH hm hv p=logDeterminant (kernelEigenvalue (perturb_integrable
hm hv p.1) hn) p.2`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
def perturbH {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (p : (ι → ℝ) × ℝ) : ℝ := by
  classical
  exact if hn : ∀ x,0≤perturb m v p.1 x then
    logDeterminant (kernelEigenvalue (perturb_integrable hm hv p.1) hn) p.2 else 0

 /--
Exact identity `perturbH hm hv p=logDeterminant (kernelEigenvalue (perturb_integrable hm hv
p.1) hn) p.2`.

Use: `«2610.05164v2».LocalObstruction.perturbH_joint_analytic` rewrites with this identity to
establish the precise assertion is `AnalyticAt ℝ (perturbH hm hv) ((0:ι → ℝ),s)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem perturbH_actual {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (p : (ι → ℝ) × ℝ)
    (hn : ∀ x,0≤perturb m v p.1 x) :
    perturbH hm hv p=logDeterminant (kernelEigenvalue (perturb_integrable hm hv p.1) hn) p.2 := by
  classical
  simp only [perturbH, dite_eq_left hn]

 /--
The precise assertion is `AnalyticAt ℝ (perturbH hm hv) ((0:ι → ℝ),s)`.

Use: `«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic` uses this assertion
to prove the bound `AnalyticAt ℝ (fun p : (ι → ℝ) × ℝ => observationH
(perturb m v p.1) p.2) (0,s)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem perturbH_joint_analytic {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hc : Continuous m) (hn : ∀ x,0<m x)
    (hv : ∀ i,Integrable (v i)) (hvc : ∀ i,Continuous (v i))
    (hcomp : ∀ i,HasCompactSupport (v i)) {s : ℝ} (hs : 0<s) :
    AnalyticAt ℝ (perturbH hm hv) ((0:ι → ℝ),s) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hnp : ∀ x,0≤perturb m v (0:ι → ℝ) x := fun x => by simpa [perturb] using (hn x).le
  have hT : 0<perturbTransmission hm hv ((0:ι → ℝ),s) := by
    rw [perturbTransmission_actual hm hv _ hnp hs.le]
    exact zero_lt_one.trans_le (transmission_ge_one (perturb_integrable hm hv 0) hnp hs.le)
  have hlog := (analyticAt_log hT).comp
    (f := perturbTransmission hm hv) (perturbTransmission_joint_analytic hm (fun x => (hn x).le) hv hs.le)
  apply hlog.congr
  have hpos := (continuous_fst.tendsto ((0:ι → ℝ),s)).eventually
    (finite_perturbation_positive hc hn hvc hcomp)
  have hspos := (continuous_snd.tendsto ((0:ι → ℝ),s)).eventually (Ioi_mem_nhds hs)
  filter_upwards [hpos,hspos] with p hp hsp
  dsimp only [Function.comp_def]
  rw [perturbH_actual hm hv p (fun x => (hp x).le),
    perturbTransmission_actual hm hv p (fun x => (hp x).le) hsp.le,
    log_transmission_eq_logDeterminant (perturb_integrable hm hv p.1) (fun x => (hp x).le) hsp.le]

end
end «2610.05164v2».LocalObstruction
