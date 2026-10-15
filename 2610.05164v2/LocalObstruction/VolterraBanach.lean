import «2610.05164v2».HalfLine.GreenVolterra
import «2610.05164v2».Filters.VolterraUniqueness
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
Article: 2610.05164v2, Lemma 26.
The literal Volterra operator on the Banach space of bounded continuous functions.
Use: `«2610.05164v2».LocalObstruction.volterraMap` feeds
`«2610.05164v2».LocalObstruction.volterraMap_affine` (volterra Map affine).
Proof chain: `«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic` — 2610.05164v2,
Theorem 6.1; No locally sharp C1 bound from finitely many spectral observations.
Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation. The needed form is proved here.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real «2610.05164v2».Filters «2610.05164v2».HalfLine
open scoped Topology BoundedContinuousFunction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
Defines `VolterraSpace` of type `` by `ℝ →ᵇ ℝ`.

Use: `«2610.05164v2».LocalObstruction.volterraBCF` uses this definition in the displayed
construction of `volterraBCF`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.
-/
abbrev VolterraSpace := ℝ →ᵇ ℝ

 /--
Membership in the specified domain/enclosure: `volterraKernel x y∈Icc (0:ℝ) 1`.

Use: `«2610.05164v2».LocalObstruction.volterra_banach_bound` rewrites with this assertion to
establish the stated quantitative bound `‖volterra 1 m f x‖≤((∫ y,|m y|)/2)*‖f‖`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Separate `y<x` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem volterraKernel_bounds (x y : ℝ) : volterraKernel x y∈Icc (0:ℝ) 1 := by
  by_cases hy : y<x
  · have he : exp (-2*(x-y))≤1 := exp_le_one_iff.mpr (by linarith)
    simp only [volterraKernel,indicator_of_mem (show y∈Iio x from hy)]
    exact ⟨by linarith,by linarith [exp_pos (-2*(x-y))]⟩
  · simp [volterraKernel,hy]

 /--
The stated quantitative bound `‖volterra 1 m f x‖≤((∫ y,|m y|)/2)*‖f‖`.

Use: `«2610.05164v2».LocalObstruction.volterraBCF` uses this bound in the displayed
construction of `volterraBCF`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: Use the identities/estimates `«2610.05164v2».Filters.bounded_forcing_integrable`,
`«2610.05164v2».HalfLine.volterra_full_integral`,
`«2610.05164v2».HalfLine.volterraKernel_mul_integrable` with the arguments shown in the proof.
-/
theorem volterra_banach_bound {m : ℝ → ℝ} (hm : Integrable m) (f : VolterraSpace) (x : ℝ) :
    ‖volterra 1 m f x‖≤((∫ y,|m y|)/2)*‖f‖ := by
  -- Use the identities/estimates `«2610.05164v2».Filters.bounded_forcing_integrable`,
  -- `«2610.05164v2».HalfLine.volterra_full_integral`,
  -- `«2610.05164v2».HalfLine.volterraKernel_mul_integrable` with the arguments shown in the
  -- proof.
  have hj := bounded_forcing_integrable hm f.continuous.aestronglyMeasurable f.norm_coe_le_norm
  rw [volterra_full_integral hj,norm_mul,Real.norm_eq_abs]
  norm_num
  have hi := volterraKernel_mul_integrable hj x
  have hdom : (∫ y,‖volterraKernel x y*(m y*f y)‖)≤
      (∫ y,|m y|)*‖f‖ := by
    rw [← integral_mul_const]
    apply integral_mono_ae hi.norm (hm.norm.mul_const _)
    exact Filter.Eventually.of_forall (fun y => by
      dsimp only
      rw [norm_mul,norm_mul,Real.norm_eq_abs,abs_of_nonneg (volterraKernel_bounds x y).1]
      calc
        _ ≤ ‖m y‖*‖f y‖ := mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (volterraKernel_bounds x y).2
        _ ≤ _ := mul_le_mul_of_nonneg_left (f.norm_coe_le_norm y) (norm_nonneg _))
  have hn := norm_integral_le_integral_norm (μ := volume) (fun y => volterraKernel x y*(m y*f y))
  rw [Real.norm_eq_abs] at hn
  nlinarith

 /--
Defines `volterraBCF` of type `VolterraSpace` by
`BoundedContinuousFunction.ofNormedAddCommGroup (volterra 1 m f) (volterra_continuous
(bounded_forcing_integrable hm f.continuous.aestronglyMeasurable f.norm_coe_le_norm) 1) (((∫
y,|m y|)/2)*‖f‖) (volterra_banach_bound hm f)`.

Use: `«2610.05164v2».LocalObstruction.volterraLinear` uses this definition in the displayed
construction of `volterraLinear`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.
-/
def volterraBCF {m : ℝ → ℝ} (hm : Integrable m) (f : VolterraSpace) : VolterraSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup (volterra 1 m f)
    (volterra_continuous (bounded_forcing_integrable hm f.continuous.aestronglyMeasurable f.norm_coe_le_norm) 1)
    (((∫ y,|m y|)/2)*‖f‖) (volterra_banach_bound hm f)

 /--
Exact identity `volterraBCF hm f x=volterra 1 m f x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 26.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem volterraBCF_apply {m : ℝ → ℝ} (hm : Integrable m) (f : VolterraSpace) (x : ℝ) :
    volterraBCF hm f x=volterra 1 m f x := rfl

 /--
Constructs `volterraLinear` of type `VolterraSpace →ₗ[ℝ] VolterraSpace` by the displayed record
fields. Data fields specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».LocalObstruction.volterraMap` uses this definition in the displayed
construction of `volterraMap`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.
-/
def volterraLinear {m : ℝ → ℝ} (hm : Integrable m) : VolterraSpace →ₗ[ℝ] VolterraSpace where
  toFun := volterraBCF hm
  map_add' f g := by
    apply BoundedContinuousFunction.ext
    intro x
    have hf := bounded_forcing_integrable hm f.continuous.aestronglyMeasurable f.norm_coe_le_norm
    have hg := bounded_forcing_integrable hm g.continuous.aestronglyMeasurable g.norm_coe_le_norm
    have hfg : Integrable (fun y => m y*(f y+g y)) := by
      convert! hf.add hg using 1
      funext y
      change m y*(f y+g y)=m y*f y+m y*g y
      ring
    change volterra 1 m (fun y => f y+g y) x=volterra 1 m f x+volterra 1 m g x
    rw [volterra_full_integral hfg,volterra_full_integral hf,volterra_full_integral hg]
    have he : (fun y => volterraKernel x y*(m y*(f y+g y)))=
        fun y => volterraKernel x y*(m y*f y)+volterraKernel x y*(m y*g y) := by
      funext y
      ring
    rw [he,integral_add (volterraKernel_mul_integrable hf x) (volterraKernel_mul_integrable hg x)]
    ring
  map_smul' a f := by
    apply BoundedContinuousFunction.ext
    intro x
    have hf := bounded_forcing_integrable hm f.continuous.aestronglyMeasurable f.norm_coe_le_norm
    have ha : Integrable (fun y => m y*(a*f y)) := by
      convert! hf.const_mul a using 1
      funext y
      change m y*(a*f y)=a*(m y*f y)
      ring
    change volterra 1 m (fun y => a*f y) x=a*volterra 1 m f x
    rw [volterra_full_integral ha,volterra_full_integral hf]
    have he : (fun y => volterraKernel x y*(m y*(a*f y)))=
        fun y => a*(volterraKernel x y*(m y*f y)) := by
      funext y
      ring
    rw [he,integral_const_mul]
    ring

 /--
Defines `volterraMap` of type `VolterraSpace →L[ℝ] VolterraSpace` by `(volterraLinear
hm).mkContinuous ((∫ y,|m y|)/2) (fun f => (BoundedContinuousFunction.norm_le (by
positivity)).mpr (volterra_banach_bound hm f))`.

Use: `«2610.05164v2».LocalObstruction.volterraMap_apply` uses this definition to establish
exact identity `volterraMap hm f x=volterra 1 m f x`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.
-/
def volterraMap {m : ℝ → ℝ} (hm : Integrable m) : VolterraSpace →L[ℝ] VolterraSpace :=
  (volterraLinear hm).mkContinuous ((∫ y,|m y|)/2) (fun f =>
    (BoundedContinuousFunction.norm_le (by positivity)).mpr (volterra_banach_bound hm f))

 /--
Exact identity `volterraMap hm f x=volterra 1 m f x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 26.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem volterraMap_apply {m : ℝ → ℝ} (hm : Integrable m) (f : VolterraSpace) (x : ℝ) :
    volterraMap hm f x=volterra 1 m f x := rfl

end
end «2610.05164v2».LocalObstruction
