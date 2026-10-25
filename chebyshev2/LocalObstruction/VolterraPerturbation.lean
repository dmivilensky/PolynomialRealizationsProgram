import chebyshev2.LocalObstruction.VolterraBanach
import chebyshev2.LocalObstruction.CompactPerturbation
import Mathlib.Analysis.Analytic.Linear

/-!
Article: chebyshev2, Lemma 26.
Finite signed density perturbations are a polynomial family of literal Volterra operators on one
fixed Banach space.
Use: `chebyshev2.LocalObstruction.volterraPencil_joint_analytic` feeds
`chebyshev2.LocalObstruction.volterraSolution_signed_joint_analytic` (volterra Solution signed
joint analytic).
Proof chain: `chebyshev2.LocalObstruction.observationH_finite_joint_analytic` — chebyshev2,
Theorem 6.1; No locally sharp C1 bound from finitely many spectral observations.
Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation. The needed form is proved here.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Set MeasureTheory Real chebyshev2.Filters chebyshev2.HalfLine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
Supplies the typeclass structure specified by `IsBoundedSMul ℝ (VolterraSpace →L[ℝ]
VolterraSpace)`. This lets subsequent generic library results apply to this concrete type.

Use: supplies this typeclass to generic library results in the module; instance resolution
inserts it where required by their signatures.

Article: chebyshev2, Lemma 26.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
local instance : IsBoundedSMul ℝ (VolterraSpace →L[ℝ] VolterraSpace) :=
  by convert! (IsBoundedSMul.of_norm_smul_le (fun (r : ℝ) (f : VolterraSpace →L[ℝ] VolterraSpace) =>
    ContinuousLinearMap.opNorm_smul_le r f)) using 1

 /--
Integrability of the displayed function: `Integrable (perturb m v a)`.

Use: `chebyshev2.LocalObstruction.volterraMap_perturb` uses this integrability result to
establish exact identity `volterraMap (perturb_integrable hm hv a)=volterraMap hm+∑ i,a i •
volterraMap (hv i)`.

Article: chebyshev2, Theorem 6.1 via
`chebyshev2.LocalObstruction.observationH_finite_joint_analytic`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem perturb_integrable {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (a : ι → ℝ) : Integrable (perturb m v a) :=
  hm.add (integrable_finsetSum _ (fun i _ => (hv i).const_mul (a i)))

 /--
Exact identity `volterraMap (perturb_integrable hm hv a)=volterraMap hm+∑ i,a i • volterraMap
(hv i)`.

Use: `chebyshev2.LocalObstruction.volterraPencil_joint_analytic` rewrites with this
identity to prove the bound `AnalyticAt ℝ (fun z : (ι → ℝ) × ℝ =>
volterraPencil (perturb_integrable hm hv z.1) z.2) p`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem volterraMap_perturb {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (a : ι → ℝ) :
    volterraMap (perturb_integrable hm hv a)=volterraMap hm+∑ i,a i • volterraMap (hv i) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  apply ContinuousLinearMap.ext
  intro f
  apply BoundedContinuousFunction.ext
  intro x
  have hbase := bounded_forcing_integrable hm f.continuous.aestronglyMeasurable f.norm_coe_le_norm
  have hdir (i : ι) := bounded_forcing_integrable (hv i) f.continuous.aestronglyMeasurable f.norm_coe_le_norm
  have hp := bounded_forcing_integrable (perturb_integrable hm hv a) f.continuous.aestronglyMeasurable f.norm_coe_le_norm
  simp only [add_apply,sum_apply,smul_apply,BoundedContinuousFunction.coe_add,
    BoundedContinuousFunction.coe_sum,BoundedContinuousFunction.coe_smul,
    Pi.add_apply,Finset.sum_apply,smul_eq_mul,volterraMap_apply]
  rw [volterra_full_integral hp,volterra_full_integral hbase]
  have he : (fun y => volterraKernel x y*(perturb m v a y*f y))=
      fun y => volterraKernel x y*(m y*f y)+∑ i,a i*(volterraKernel x y*(v i y*f y)) := by
    funext y
    unfold perturb
    rw [add_mul,mul_add,Finset.sum_mul,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,integral_add (volterraKernel_mul_integrable hbase x)
    (integrable_finsetSum _ (fun i _ => (volterraKernel_mul_integrable (hdir i) x).const_mul (a i))),
    integral_finsetSum _ (fun i _ => (volterraKernel_mul_integrable (hdir i) x).const_mul (a i))]
  simp only [integral_const_mul]
  simp_rw [volterra_full_integral (hdir _)]
  rw [mul_add,Finset.mul_sum]
  apply congrArg₂ (·+·) rfl
  apply Finset.sum_congr rfl
  intro i _
  ring

 /--
Defines `volterraPencil` of type `VolterraSpace →L[ℝ] VolterraSpace` by `ContinuousLinearMap.id
ℝ VolterraSpace-s • volterraMap hm`.

Use: `chebyshev2.LocalObstruction.volterraPencil_joint_analytic` rewrites with this
definition to prove the bound `AnalyticAt ℝ (fun z : (ι → ℝ) × ℝ =>
volterraPencil (perturb_integrable hm hv z.1) z.2) p`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.
-/
def volterraPencil {m : ℝ → ℝ} (hm : Integrable m) (s : ℝ) : VolterraSpace →L[ℝ] VolterraSpace :=
  ContinuousLinearMap.id ℝ VolterraSpace-s • volterraMap hm

 /--
The stated quantitative bound `AnalyticAt ℝ (fun z : (ι → ℝ) × ℝ => volterraPencil
(perturb_integrable hm hv z.1) z.2) p`.

Use: `chebyshev2.LocalObstruction.volterraSolution_joint_analytic` uses this identity to
establish the precise assertion is `AnalyticAt ℝ (volterraSolution hm hv) ((0:ι → ℝ),s)`.

Article: chebyshev2, Lemma 26 via
`chebyshev2.LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem volterraPencil_joint_analytic {ι : Type*} [Fintype ι] {m : ℝ → ℝ} {v : ι → ℝ → ℝ}
    (hm : Integrable m) (hv : ∀ i,Integrable (v i)) (p : (ι → ℝ) × ℝ) :
    AnalyticAt ℝ (fun z : (ι → ℝ) × ℝ => volterraPencil (perturb_integrable hm hv z.1) z.2) p := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : (fun z : (ι → ℝ) × ℝ => volterraPencil (perturb_integrable hm hv z.1) z.2)=
      fun z => ContinuousLinearMap.id ℝ VolterraSpace-
        z.2 • (volterraMap hm+∑ i,z.1 i • volterraMap (hv i)) := by
    funext z
    rw [volterraPencil,volterraMap_perturb]
  rw [he]
  apply analyticAt_const.sub
  apply analyticAt_snd.smul
  apply analyticAt_const.add
  have h := Finset.analyticAt_sum Finset.univ (f := fun i (z : (ι → ℝ) × ℝ) =>
    z.1 i • volterraMap (hv i)) (fun i _ =>
      (((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).analyticAt p.1).comp analyticAt_fst).smul analyticAt_const)
  convert! h using 1
  funext z
  simp only [Finset.sum_apply]

end
end chebyshev2.LocalObstruction
