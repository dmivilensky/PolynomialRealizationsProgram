import jacobi.Rearrangement.ReflectionCube
import jacobi.Rearrangement.RieszPolarization

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
The finite graph partition inequality is integrated on the actual real product
space. The kernel factors are the article's exponentials, and all integrals are
absolutely convergent. Specializing the graph to a cycle gives the elementary
polarization comparison for every G_p without additional analytic assumptions.
Source: the reflection-orbit proof of Brascamp–Lieb–Luttinger.
Use: cycles recover exactly the product integrands for the spectral moments.
-/
namespace jacobi.Rearrangement
noncomputable section
open MeasureTheory Real Set jacobi.Variational
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/-- Product of density factors and exponential interactions on a finite graph.
Use: cycles recover exactly the product integrands for the spectral moments.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def graphIntegrand {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (m : ℝ → ℝ) (z : V → ℝ) : ℝ :=
  (∏ v, m (z v))*∏ e, exp (-|z (left e)-z (right e)|)

/-- The independent density product dominates every graph integrand.
Use: proves actual L1 integrability before the graph comparison is integrated.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: all exponential factors lie in (0,1], so their finite product is at most one. -/
theorem graphIntegrand_bound {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (m : ℝ → ℝ) (z : V → ℝ) :
    |graphIntegrand left right m z| ≤ ∏ v, |m (z v)| := by
  -- The number and arrangement of edges do not affect the independent-coordinate L1 majorant.
  have hn : 0 ≤ ∏ e : E, exp (-|z (left e)-z (right e)|) :=
    Finset.prod_nonneg (fun _ _ => (exp_pos _).le)
  have hb : (∏ e : E, exp (-|z (left e)-z (right e)|)) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => (exp_pos _).le)
      (fun _ _ => exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _)))
  rw [graphIntegrand,abs_mul,Finset.abs_prod,abs_of_nonneg hn]
  exact mul_le_of_le_one_right (Finset.prod_nonneg (fun _ _ => abs_nonneg _)) hb

/-- All finite graph integrals of a measurable L1 density are absolutely convergent.
Use: genuine Bochner integration of the graph partition comparison.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the independent product of |m| is integrable by finite-product Fubini,
and the kernel integrand is measurable and bounded by that product. -/
theorem graphIntegrand_integrable {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) {m : ℝ → ℝ} (hm : Integrable m) (hmm : Measurable m) :
    Integrable (graphIntegrand left right m) := by
  -- Each physical coordinate supplies one independent integrable density factor.
  have hi : Integrable (fun z : V → ℝ => ∏ v, |m (z v)|) :=
    Integrable.fintype_prod (fun _ => hm.abs)
  apply hi.mono'
  · have hmeas : Measurable (graphIntegrand left right m) := by
      unfold graphIntegrand
      fun_prop
    exact hmeas.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using graphIntegrand_bound left right m z

/-- A reflected kernel link depends only on equality or inequality of its two spins.
Use: identifies the actual kernel product with the same-side graph partition coefficients.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: enumerate the two spins; simultaneous reflection preserves distance
and the two cross-reflected distances coincide. -/
theorem spin_kernel (a x y : ℝ) (σ τ : ZMod 2) :
    exp (-|spinCoordinate a σ x-spinCoordinate a τ y|)=
      if σ=τ then exp (-|x-y|) else exp (-|x-reflect a y|) := by
  -- The four spin choices give exactly the two geometrically distinct distances.
  have hs : |reflect a x-reflect a y|=|x-y| := by
    rw [show reflect a x-reflect a y=-(x-y) by dsimp [reflect]; ring,abs_neg]
  have hc : |reflect a x-y|=|x-reflect a y| := by
    rw [show reflect a x-y=-(x-reflect a y) by dsimp [reflect]; ring,abs_neg]
  rcases spin_cases σ with rfl | rfl <;> rcases spin_cases τ with rfl | rfl <;>
    simp only [spinCoordinate_zero,spinCoordinate_one,hs,hc] <;> split_ifs <;> simp_all

/-- The actual graph integrand on a reflected tuple is the finite spin partition summand.
Use: transfers the proved finite graph comparison to real multiple integrals.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: each vertex selects one of the density values, and each edge uses the proved two-spin kernel identity. -/
theorem graphIntegrand_reflect {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (m : ℝ → ℝ) (a : ℝ) (σ : V → ZMod 2) (z : V → ℝ) :
    graphIntegrand left right m (cubeReflection a σ z)=
      (∏ v, if σ v=0 then m (z v) else m (reflect a (z v)))*
        ∏ e, if σ (left e)=σ (right e) then exp (-|z (left e)-z (right e)|)
          else exp (-|z (left e)-reflect a (z (right e))|) := by
  -- Keep each vertex and edge factor attached to its original physical coordinate.
  unfold graphIntegrand
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    change m (spinCoordinate a (σ v) (z v))=_
    unfold spinCoordinate
    split_ifs <;> rfl
  · apply Finset.prod_congr rfl
    intro e _
    exact spin_kernel a (z (left e)) (z (right e)) (σ (left e)) (σ (right e))

/-- On the preferred half-space, the actual graph reflection orbit increases under polarization.
Use: establishes every cyclic moment's pointwise orbit comparison before integration.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: both density values are nonnegative, the exponential edge coefficients
obey the reflection distance order, and polarization sorts every vertex pair. -/
theorem graph_orbit_left {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (m : Density) (a : ℝ) (z : V → ℝ) (hz : ∀ v, z v ≤ a) :
    cubeOrbit (graphIntegrand left right m.value) a z ≤
      cubeOrbit (graphIntegrand left right (m.polarize a).value) a z := by
  -- The finite theorem permits arbitrary graphs, so it covers cycles and their repeated edges uniformly.
  have H := graph_partition_sorted left right (fun v => m.value (z v))
    (fun v => m.value (reflect a (z v)))
    (fun e => exp (-|z (left e)-z (right e)|))
    (fun e => exp (-|z (left e)-reflect a (z (right e))|))
    (fun _ => m.nonneg _) (fun _ => m.nonneg _) (fun _ => (exp_pos _).le)
    (fun e => exp_le_exp.mpr (neg_le_neg (reflection_distance (hz (left e)) (hz (right e)))))
  have he : cubeOrbit (graphIntegrand left right m.value) a z =
      ∑ σ : V → ZMod 2, (∏ v, if σ v=0 then m.value (z v) else m.value (reflect a (z v)))*
        ∏ e, if σ (left e)=σ (right e) then exp (-|z (left e)-z (right e)|)
          else exp (-|z (left e)-reflect a (z (right e))|) := by
    unfold cubeOrbit
    exact Finset.sum_congr rfl (fun σ _ => graphIntegrand_reflect left right m.value a σ z)
  rw [he]
  refine H.trans_eq ?_
  unfold cubeOrbit
  apply Finset.sum_congr rfl
  intro σ _
  rw [graphIntegrand_reflect]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  change (if σ v=0 then max (m.value (z v)) (m.value (reflect a (z v)))
    else min (m.value (z v)) (m.value (reflect a (z v)))) =
      if σ v=0 then polarize a m.value (z v) else polarize a m.value (reflect a (z v))
  rw [(polarize_left_pair a m.value (hz v)).1,(polarize_left_pair a m.value (hz v)).2]

/-- Polarization increases the full graph orbit at an arbitrary physical tuple.
Use: monotone integration on the whole product space, without any symmetry assumption on the density.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: reflect each coordinate into the preferred half-line and use invariance
of each complete orbit under changing its representative. -/
theorem graph_orbit {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (m : Density) (a : ℝ) (z : V → ℝ) :
    cubeOrbit (graphIntegrand left right m.value) a z ≤
      cubeOrbit (graphIntegrand left right (m.polarize a).value) a z := by
  -- Different coordinates may start on different sides; normalize them independently.
  let τ (v : V) : ZMod 2 := if z v ≤ a then 0 else 1
  have hz (v : V) : cubeReflection a τ z v ≤ a := by
    change spinCoordinate a (τ v) (z v) ≤ a
    dsimp only [τ]
    by_cases h : z v ≤ a
    · rw [ite_eq_left h,spinCoordinate_zero]
      exact h
    · rw [ite_eq_right h,spinCoordinate_one]
      dsimp [reflect]
      linarith
  have H := graph_orbit_left left right m a (cubeReflection a τ z) hz
  simpa only [cubeOrbit_reflect] using H

/-- Every finite exponential graph integral increases under simultaneous density polarization.
Use: specializes to the full cyclic moment inequalities at every order.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: integrate the genuine orbit comparison using proved absolute convergence,
replace orbit integrals by 2^|V| times their originals, and cancel the positive factor. -/
theorem graph_integral_polarize {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (m : Density) (a : ℝ) :
    (∫ z, graphIntegrand left right m.value z) ≤
      ∫ z, graphIntegrand left right (m.polarize a).value z := by
  -- The nonnegative graph comparison is applied to the actual integrable functions on R^|V|.
  have hi := graphIntegrand_integrable left right m.integrable m.measurable
  have hp := graphIntegrand_integrable left right (m.polarize a).integrable (m.polarize a).measurable
  have H := integral_mono (cubeOrbit_integrable hi a) (cubeOrbit_integrable hp a)
    (graph_orbit left right m a)
  rw [integral_cubeOrbit hi a,integral_cubeOrbit hp a] at H
  exact (mul_le_mul_iff_of_pos_left (by positivity : 0 < (2 : ℝ)^Fintype.card V)).mp H

end
end jacobi.Rearrangement
