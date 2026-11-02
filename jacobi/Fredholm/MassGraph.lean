import jacobi.Fredholm.MassCurveDirection
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

/-!
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
The actual mass level has a genuine differentiable graph near every
physical interior point. Positive mass partials discharge the implicit
function theorem's invertibility requirement; uniqueness identifies its
local graph with a single global root selector.
Source: the classical implicit function theorem for continuous partial derivatives.
Use: joins the locally constructed implicit graphs into the single source constant-mass curve.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Elliptic
open scoped Topology Classical
set_option backward.isDefEq.respectTransparency false

/-- The physical chi root of the actual mass equation, when one exists.
Use: joins the locally constructed implicit graphs into the single source constant-mass curve.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
-/
def massParameter (M t : ℝ) : ℝ :=
  if h : ∃ c : ℝ,c∈Ioo (0:ℝ) 1 ∧ mass t c=M then h.choose else 0

/-- A physical root of the literal mass equation is exactly the selected mass parameter.
Use: uniqueness of mass roots identifies every local implicit graph with the global selector.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: strict chi monotonicity of the actual mass gives injectivity on
the physical interval; compare the selected root with the given one. -/
theorem massParameter_eq {M t c : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) (hm : mass t c=M) : massParameter M t=c := by
  -- The selector uses existence only; strict monotonicity proves that its choice is immaterial.
  have h : ∃ v : ℝ,v∈Ioo (0:ℝ) 1 ∧ mass t v=M := ⟨c,hc,hm⟩
  rw [massParameter,dite_eq_left h]
  have hs := h.choose_spec
  exact (mass_parameter_strictMono ⟨ht.1.le,ht.2.le⟩).injOn
    ⟨hs.1.1.le,hs.1.2.le⟩ ⟨hc.1.le,hc.2.le⟩ (hs.2.trans hm.symm)

/-- The actual mass equation has a genuine local differentiable physical solution at each interior root.
Use: proves existence and regularity of the source mass curve, rather than assuming a candidate graph.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the verified actual mass partials are continuous and its chi
partial is positive. Construct an explicit inverse for that scalar
linear map and invoke the bivariate implicit function theorem.
Its derivative and limit provide the true local graph and its physical range. -/
theorem local_mass_graph {t c : ℝ} (ht : t∈Ioo (0:ℝ) 1) (hc : c∈Ioo (0:ℝ) 1) :
    ∃ k : ℝ → ℝ,DifferentiableAt ℝ k t ∧ k t=c ∧
      ∀ᶠ u in 𝓝 t,k u∈Ioo (0:ℝ) 1 ∧ mass u (k u)=mass t c := by
  -- The implicit function's derivative is obtained from the actual continuous mass gradient.
  let S := ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)
  let f1 := fun u v : ℝ => S (massGradient u v).1
  let f2 := fun u v : ℝ => S (massGradient u v).2
  have hn : Ioo (0:ℝ) 1×ˢIoo (0:ℝ) 1∈𝓝 (t,c) :=
    prod_mem_nhds (isOpen_Ioo.mem_nhds ht) (isOpen_Ioo.mem_nhds hc)
  have hd1 : ∀ᶠ p in 𝓝 (t,c),HasFDerivAt (fun u => mass u p.2) (f1 p.1 p.2) p.1 := by
    filter_upwards [hn] with p hp
    exact (mass_shape_hasDerivAt_pos hp.1 ⟨hp.2.1,hp.2.2.le⟩).1.hasFDerivAt
  have hd2 : ∀ᶠ p in 𝓝 (t,c),HasFDerivAt (mass p.1) (f2 p.1 p.2) p.2 := by
    filter_upwards [hn] with p hp
    exact (mass_parameter_hasDerivAt ⟨hp.1.1.le,hp.1.2.le⟩ hp.2).hasFDerivAt
  have hG := (gradients_continuousAt ht hc).1
  have h1 : ContinuousAt (fun p : ℝ×ℝ => f1 p.1 p.2) (t,c) := S.continuous.continuousAt.comp hG.fst
  have h2 : ContinuousAt (fun p : ℝ×ℝ => f2 p.1 p.2) (t,c) := S.continuous.continuousAt.comp hG.snd
  have hi : (f2 t c).IsInvertible := by
    have hpos := (massGradient_pos ht hc).2
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := S ((massGradient t c).2)⁻¹)
    · apply ContinuousLinearMap.ext
      intro v
      change (v*((massGradient t c).2)⁻¹)*(massGradient t c).2=v
      field_simp [hpos.ne']
    · apply ContinuousLinearMap.ext
      intro v
      change (v*(massGradient t c).2)*((massGradient t c).2)⁻¹=v
      field_simp [hpos.ne']
  let k := implicitFunctionOfBivariate hd1 hd2 h1 h2 hi
  have hk := hasStrictFDerivAt_implicitFunctionOfBivariate hd1 hd2 h1 h2 hi
  have hl := tendsto_implicitFunctionOfBivariate hd1 hd2 h1 h2 hi
  have he := eventually_apply_implicitFunctionOfBivariate hd1 hd2 h1 h2 hi
  have hk0 : k t=c := tendsto_nhds_unique hk.continuousAt.tendsto hl
  refine ⟨k,hk.hasFDerivAt.differentiableAt,hk0,?_⟩
  filter_upwards [hl.eventually (isOpen_Ioo.mem_nhds hc),he] with u hu heq
  exact ⟨hu,heq⟩

/-- The globally selected physical mass root is genuinely differentiable at every actual interior root.
Use: joins local implicit graphs without assuming connectedness or differentiability of a proposed candidate curve.
Article: jacobi, Appendix D.4 (envelope identities and global parameter uniqueness).
Proof: the local implicit function stays physical and has the required
actual mass. Strict mass monotonicity identifies it with the root selector
on a full neighborhood. Transfer its ordinary derivative and the derivative
of the locally constant restricted mass to the selector. -/
theorem massParameter_calculus {M t c : ℝ} (ht : t∈Ioo (0:ℝ) 1)
    (hc : c∈Ioo (0:ℝ) 1) (hm : mass t c=M) :
    ∃ b : ℝ,HasDerivAt (massParameter M) b t ∧
      HasDerivAt (fun u => mass u (massParameter M u)) 0 t := by
  -- The same selector agrees locally with a genuine implicit function supplied by the theorem.
  obtain ⟨k,hkd,hkt,hke⟩ := local_mass_graph ht hc
  have he : massParameter M=ᶠ[𝓝 t] k := by
    filter_upwards [hke,isOpen_Ioo.mem_nhds ht] with u hu hut
    exact massParameter_eq hut hu.1 (hu.2.trans hm)
  refine ⟨deriv k t,hkd.hasDerivAt.congr_of_eventuallyEq he,?_⟩
  apply (hasDerivAt_const t M).congr_of_eventuallyEq
  filter_upwards [he,hke] with u hue hku
  rw [hue,hku.2,hm]

end
end jacobi.Fredholm
