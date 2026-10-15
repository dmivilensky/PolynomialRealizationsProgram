import «2610.05164v2».LocalObstruction.VolterraBanach

/-!
Article: 2610.05164v2, Lemma 26.
L1 density pairing as a continuous functional on bounded continuous functions, used to recover the
actual Jost transmission from the inverse.
Use: `«2610.05164v2».LocalObstruction.jostBCF` feeds `«2610.05164v2».LocalObstruction.jostBCF_apply`
(jost BCF apply).
Proof chain: `«2610.05164v2».LocalObstruction.observationH_finite_joint_analytic` — 2610.05164v2,
Theorem 6.1; No locally sharp C1 bound from finitely many spectral observations.
Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation. The needed form is proved here.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open MeasureTheory Real «2610.05164v2».Filters
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

 /--
Constructs `volterraMassLinear` of type `VolterraSpace →ₗ[ℝ] ℝ` by the displayed record fields.
Data fields specify the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».LocalObstruction.volterraMass` uses this definition in the displayed
construction of `volterraMass`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.
-/
def volterraMassLinear {m : ℝ → ℝ} (hm : Integrable m) : VolterraSpace →ₗ[ℝ] ℝ where
  toFun f := ∫ x,m x*f x
  map_add' f g := by
    change (∫ x,m x*(f x+g x))=(∫ x,m x*f x)+(∫ x,m x*g x)
    simp only [mul_add]
    exact integral_add
      (bounded_forcing_integrable hm f.continuous.aestronglyMeasurable f.norm_coe_le_norm)
      (bounded_forcing_integrable hm g.continuous.aestronglyMeasurable g.norm_coe_le_norm)
  map_smul' a f := by
    change (∫ x,m x*(a*f x))=a*(∫ x,m x*f x)
    simp_rw [mul_left_comm (m _) a,integral_const_mul]

 /--
Defines `volterraMass` of type `VolterraSpace →L[ℝ] ℝ`. The displayed construction fixes its
component data; its proof fields enforce the listed compatibility properties.

Use: `«2610.05164v2».LocalObstruction.volterraMass_apply` uses this definition to establish
exact identity `volterraMass hm f=∫ x,m x*f x`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.
-/
def volterraMass {m : ℝ → ℝ} (hm : Integrable m) : VolterraSpace →L[ℝ] ℝ :=
  (volterraMassLinear hm).mkContinuous (∫ x,|m x|) (fun f => by
    change ‖∫ x,m x*f x‖≤(∫ x,|m x|)*‖f‖
    apply (norm_integral_le_integral_norm _).trans
    rw [← integral_mul_const]
    apply integral_mono_ae
      (bounded_forcing_integrable hm f.continuous.aestronglyMeasurable f.norm_coe_le_norm).norm
      (hm.norm.mul_const _)
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)))

 /--
Exact identity `volterraMass hm f=∫ x,m x*f x`.

Use: `«2610.05164v2».LocalObstruction.groundLeftAmplitude_mass` rewrites with this identity to
establish exact identity `groundLeftAmplitude G=groundParameter hm hn/2*volterraMass hm
(groundLeft G hM)`.

Article: 2610.05164v2, Theorem 6.1 via
`«2610.05164v2».LocalObstruction.groundObservationWitness`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem volterraMass_apply {m : ℝ → ℝ} (hm : Integrable m) (f : VolterraSpace) :
    volterraMass hm f=∫ x,m x*f x := rfl

 /--
Defines `jostBCF` of type `VolterraSpace` by `BoundedContinuousFunction.ofNormedAddCommGroup
(jost s m) (jost_continuous hm hn hs) (exp (s*(∫ x,m x)/2)) (fun x => by rw
[Real.norm_eq_abs,abs_of_pos (jost_positive hm hn hs x)] exact jost_uniform_bound hm hn hs x)`.

Use: `«2610.05164v2».LocalObstruction.jostBCF_apply` uses this definition to establish exact
identity `jostBCF hm hn hs x=jost s m x`.

Article: 2610.05164v2, Lemma 26 via
`«2610.05164v2».LocalObstruction.observation_analytic_neighborhood`.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.
-/
def jostBCF {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x) {s : ℝ} (hs : 0≤s) : VolterraSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup (jost s m) (jost_continuous hm hn hs)
    (exp (s*(∫ x,m x)/2)) (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (jost_positive hm hn hs x)]
      exact jost_uniform_bound hm hn hs x)

 /--
Exact identity `jostBCF hm hn hs x=jost s m x`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 26.

Source: Teschl, Ordinary Differential Equations and Dynamical Systems — Volterra series, causal
inverses and resolvent differentiation.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem jostBCF_apply {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ x,0≤m x) {s : ℝ} (hs : 0≤s) (x : ℝ) :
    jostBCF hm hn hs x=jost s m x := rfl

end
end «2610.05164v2».LocalObstruction
