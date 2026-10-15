import «2610.05164v2».HalfLine.GroundResolvent
import «2610.05164v2».HalfLine.JostResolvent

/-!
Article: 2610.05164v2, Theorem 3.3.
Profiles.
Result: `«2610.05164v2».HalfLine.jostProfile_left_limit` supplies the stated article conclusion.
-/
namespace «2610.05164v2».HalfLine
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».Continuum «2610.05164v2».Sobolev «2610.05164v2».GroundState
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `groundProfile G x x=1`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 3.3.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem groundProfile_boundary {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) (x : ℝ) : groundProfile G x x=1 :=
  div_self (G.positive x).ne'

/--
The actual derivative at the stated point: `HasDerivAt (groundProfile G x) (1-G.q x) x`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.3.

Proof: Use the identities/estimates `«2610.05164v2».GroundState.GroundWitness.coordinate_eq`
with the arguments shown in the proof.
-/
theorem groundProfile_boundary_derivative {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) (x : ℝ) : HasDerivAt (groundProfile G x) (1-G.q x) x := by
  convert (G.derivative x).div_const (H1.rep G.u x) using 1
  · rfl
  · rw [G.coordinate_eq]
    change 1-(1-G.d x/H1.rep G.u x)=G.d x/H1.rep G.u x
    ring

/--
Convergence along the specified source filter to the specified limit: `Tendsto (groundProfile G
x) atBot (𝓝 0)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 3.3.

Proof: Use the identities/estimates `«2610.05164v2».Sobolev.H1.rep_tendsto_zero` with the
arguments shown in the proof.
-/
theorem groundProfile_left_limit {m : ℝ → ℝ} {hm : Integrable m} {hn : ∀ t, 0 ≤ m t}
    (G : GroundWitness hm hn) (x : ℝ) : Tendsto (groundProfile G x) atBot (𝓝 0) := by
  change Tendsto (fun t => H1.rep G.u t/H1.rep G.u x) atBot (𝓝 0)
  simpa only [zero_div] using (H1.rep_tendsto_zero G.u).2.div_const (H1.rep G.u x)

/--
Exact identity `jostProfile s m x x=1`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 3.3.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_positive` with the arguments
shown in the proof.
-/
theorem jostProfile_boundary {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : jostProfile s m x x=1 := by
  simp only [jostProfile,sub_self,exp_zero,one_mul,div_self (Filters.jost_positive hm hn hs x).ne']

/--
The actual derivative at the stated point: `HasDerivAt (jostProfile s m x) (1+Filters.nonlinear
s m x) x`.

Use: a standalone supporting derivative formula for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.3.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem jostProfile_boundary_derivative {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    HasDerivAt (jostProfile s m x) (1+Filters.nonlinear s m x) x := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have he : HasDerivAt (fun t : ℝ => exp (t-x)) (1:ℝ) x := by
    simpa only [id_eq,sub_zero,sub_self,exp_zero,mul_one] using ((hasDerivAt_id x).sub_const x).exp
  convert (he.mul (Filters.jost_hasDerivAt hm hn hs x)).div_const (Filters.jost s m x) using 1
  · rfl
  · simp only [sub_self,exp_zero,one_mul,Filters.nonlinear]
    field_simp [(Filters.jost_positive hm hn hs x).ne']

/--
Convergence along the specified source filter to the specified limit: `Tendsto (jostProfile s m
x) atBot (𝓝 0)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 3.3.

Proof: Use the identities/estimates `«2610.05164v2».Filters.jost_left_limit` with the arguments
shown in the proof.
-/
theorem jostProfile_left_limit {m : ℝ → ℝ} (hm : Integrable m) (hn : ∀ t, 0 ≤ m t)
    {s : ℝ} (hs : 0 ≤ s) (x : ℝ) : Tendsto (jostProfile s m x) atBot (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => exp (t-x)) atBot (𝓝 0) := by
    simpa only [exp_sub,zero_div] using tendsto_exp_atBot.div_const (exp x)
  change Tendsto (fun t => exp (t-x)*Filters.jost s m t/Filters.jost s m x) atBot (𝓝 0)
  simpa only [zero_mul,zero_div] using (he.mul (Filters.jost_left_limit hm hn hs)).div_const
    (Filters.jost s m x)

end
end «2610.05164v2».HalfLine
