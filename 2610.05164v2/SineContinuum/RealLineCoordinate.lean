import «2610.05164v2».SineContinuum.Coordinate
import «2610.05164v2».SineContinuum.EndpointLimits
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.AtTopBotIxx
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
Article: 2610.05164v2, Proposition 2.
Proposition 2's increasing bijection onto the entire real line.
Use: `«2610.05164v2».SineContinuum.T_reflect` feeds `«2610.05164v2».SineContinuum.n_even` (n even).
Proof chain: `«2610.05164v2».LocalObstruction.groundObservationWitness` — 2610.05164v2, Theorem 6.1;
No locally sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».SineContinuum
noncomputable section
open Set Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Convergence along the specified source filter to the specified limit: `Tendsto (fun t : ℝ =>
1-t) (𝓝[<] (1:ℝ)) (𝓝[>] (0:ℝ))`.

Use: `«2610.05164v2».SineContinuum.X_right_limit` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto X (𝓝[<] (1:ℝ)) atTop`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem reflect_left : Tendsto (fun t : ℝ => 1-t) (𝓝[<] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hi : Tendsto (fun t : ℝ => t) (𝓝[<] (1:ℝ)) (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using (tendsto_const_nhds (x := (1:ℝ))).sub hi
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change t < 1 at ht
    exact sub_pos.mpr ht

/--
Convergence along the specified source filter to the specified limit: `Tendsto l (𝓝[<] (1:ℝ))
(𝓝 0)`.

Use: `«2610.05164v2».SineContinuum.l_continuousOn` uses this limit to establish continuity on
the stated domain: `ContinuousOn l (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.r_left_limit`,
`«2610.05164v2».SineContinuum.reflect_left` with the arguments shown in the proof.
-/
theorem l_right_limit : Tendsto l (𝓝[<] (1:ℝ)) (𝓝 0) := by
  have he (t : ℝ) : r (1-t)=l t := by dsimp [r]; congr 1; ring
  simpa only [Function.comp_def,he] using r_left_limit.comp reflect_left

/--
Convergence along the specified source filter to the specified limit: `Tendsto r (𝓝[<] (1:ℝ))
(𝓝 0)`.

Use: `«2610.05164v2».SineContinuum.r_continuousOn` uses this limit to establish continuity on
the stated domain: `ContinuousOn r (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Lemma 5 via
`«2610.05164v2».SineContinuum.green_mercer_diagonal_uniform`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.l_left_limit`,
`«2610.05164v2».SineContinuum.reflect_left` with the arguments shown in the proof.
-/
theorem r_right_limit : Tendsto r (𝓝[<] (1:ℝ)) (𝓝 0) := l_left_limit.comp reflect_left

/--
Convergence along the specified source filter to the specified limit: `Tendsto X (𝓝[>] (0:ℝ))
atBot`.

Use: `«2610.05164v2».SineContinuum.X_right_limit` uses this limit to establish convergence
along the specified source filter to the specified limit: `Tendsto X (𝓝[<] (1:ℝ)) atTop`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem X_left_limit : Tendsto X (𝓝[>] (0:ℝ)) atBot := by
  have hr := tendsto_log_atTop.comp ratio_left_limit
  have hn := hr.const_mul_atTop_of_neg (by norm_num : (-1/2:ℝ)<0)
  apply hn.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht
  dsimp [ratio,X]
  rw [log_div (r_positive ht).ne' (l_positive ht).ne']
  ring

/--
Convergence along the specified source filter to the specified limit: `Tendsto X (𝓝[<] (1:ℝ))
atTop`.

Use: `«2610.05164v2».SineContinuum.X_surjective` uses this limit to establish the precise
assertion is `SurjOn X (Ioo (0:ℝ) 1) univ`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.X_left_limit`,
`«2610.05164v2».SineContinuum.reflect_left`, `«2610.05164v2».SineContinuum.X_reflect` with the
arguments shown in the proof.
-/
theorem X_right_limit : Tendsto X (𝓝[<] (1:ℝ)) atTop := by
  have hl := X_left_limit.comp reflect_left
  have hn := tendsto_neg_atBot_atTop.comp hl
  have he (t : ℝ) : -X (1-t)=X t := by rw [X_reflect,neg_neg]
  simpa only [Function.comp_def,he] using hn

/--
Proposition 2's increasing bijection onto the entire real line.

The precise assertion is `SurjOn X (Ioo (0:ℝ) 1) univ`.

Use: `«2610.05164v2».SineContinuum.coordinateIso` uses this assertion in the displayed
construction of `coordinateIso`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.energy`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.X_continuousOn`,
`«2610.05164v2».SineContinuum.X_left_limit`, `«2610.05164v2».SineContinuum.X_right_limit` with
the arguments shown in the proof.
-/
theorem X_surjective : SurjOn X (Ioo (0:ℝ) 1) univ := by
  apply X_continuousOn.surjOn_of_tendsto ⟨1/2,by norm_num⟩
  · exact (tendsto_comp_coe_Ioo_atBot (by norm_num : (0:ℝ)<1)).mpr X_left_limit
  · exact (tendsto_comp_coe_Ioo_atTop (by norm_num : (0:ℝ)<1)).mpr X_right_limit

/--
Defines `coordinateIso` of type `Ioo (0:ℝ) 1 ≃o ℝ` by `StrictMono.orderIsoOfSurjective (fun t
=> X t) (fun a b hab => X_strictMono a.property b.property hab) (fun x => by obtain ⟨t,ht,hX⟩
:= X_surjective (mem_univ x); exact ⟨⟨t,ht⟩,hX⟩)`.

Use: `«2610.05164v2».SineContinuum.T` uses this definition in the displayed construction of
`T`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Definition 2 via `«2610.05164v2».SineContinuum.n`.
-/
def coordinateIso : Ioo (0:ℝ) 1 ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (fun t => X t)
    (fun a b hab => X_strictMono a.property b.property hab)
    (fun x => by obtain ⟨t,ht,hX⟩ := X_surjective (mem_univ x); exact ⟨⟨t,ht⟩,hX⟩)

/--
Exact identity `coordinateIso t=X t`.

Use: `«2610.05164v2».SineContinuum.T_X` rewrites with this identity to establish the identity
`T (X t)=t`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem coordinateIso_apply (t : Ioo (0:ℝ) 1) : coordinateIso t=X t :=
  congrFun (StrictMono.coe_orderIsoOfSurjective _ _ _) t

/--
Defines `T` of type `ℝ` by `(coordinateIso.symm x : ℝ)`.

Use: `«2610.05164v2».SineContinuum.T_derivative` uses this definition to establish the actual
derivative at the stated point: `HasDerivAt T (SineJacobi.phi (T x)) x`.

Article: 2610.05164v2, Definition 2 via `«2610.05164v2».SineContinuum.n`.
-/
def T (x : ℝ) : ℝ := (coordinateIso.symm x : ℝ)

/--
Membership in the specified domain/enclosure: `T x ∈ Ioo (0:ℝ) 1`.

Use: `«2610.05164v2».SineContinuum.T_derivative` uses this assertion to establish the actual
derivative at the stated point: `HasDerivAt T (SineJacobi.phi (T x)) x`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.sine_kernel_eigenvalue`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem T_mem (x : ℝ) : T x ∈ Ioo (0:ℝ) 1 := (coordinateIso.symm x).property

/--
Exact identity `X (T x)=x`.

Use: `«2610.05164v2».SineContinuum.T_derivative` uses this identity to establish the actual
derivative at the stated point: `HasDerivAt T (SineJacobi.phi (T x)) x`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.coordinateIso_apply` with the
arguments shown in the proof.
-/
theorem X_T (x : ℝ) : X (T x)=x := by
  have h := coordinateIso.apply_symm_apply x
  rw [coordinateIso_apply] at h
  exact h

/--
Exact identity `T (X t)=t`.

Use: `«2610.05164v2».SineContinuum.T_reflect` uses this identity to establish the identity `T
(-x)=1-T x`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.coordinateIso_apply` with the
arguments shown in the proof.
-/
theorem T_X {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : T (X t)=t := by
  have h := congrArg Subtype.val (coordinateIso.symm_apply_apply ⟨t,ht⟩)
  rw [coordinateIso_apply] at h
  exact h

/--
Continuity of the displayed function: `Continuous T`.

Use: `«2610.05164v2».SineContinuum.T_derivative` uses this continuity result to establish the
actual derivative at the stated point: `HasDerivAt T (SineJacobi.phi (T x)) x`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem T_continuous : Continuous T :=
  continuous_subtype_val.comp coordinateIso.symm.toHomeomorph.continuous

/--
The precise assertion is `StrictMono T`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 2.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem T_strictMono : StrictMono T := by
  intro x y hxy
  exact coordinateIso.symm.strictMono hxy

/--
The actual derivative at the stated point: `HasDerivAt T (SineJacobi.phi (T x)) x`.

Use: `«2610.05164v2».SineContinuum.T_smooth` uses this derivative formula to establish
smoothness to the stated order: `ContDiff ℝ ∞ T`.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.X_derivative`,
`«2610.05164v2».SineContinuum.T_mem`, `«2610.05164v2».SineContinuum.X_T` with the arguments
shown in the proof.
-/
theorem T_derivative (x : ℝ) : HasDerivAt T (SineJacobi.phi (T x)) x := by
  have hd := X_derivative (T_mem x)
  have hi : ∀ᶠ y in 𝓝 x, X (T y)=y := Eventually.of_forall X_T
  simpa only [inv_inv] using HasDerivAt.of_local_left_inverse T_continuous.continuousAt hd
    (inv_ne_zero (SineJacobi.phi_pos (T_mem x)).ne') hi

/--
Exact identity `T (-x)=1-T x`.

Use: `«2610.05164v2».SineContinuum.n_even` rewrites with this identity to establish exact
identity `n (-x)=n x`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Proof: Use the identities/estimates `«2610.05164v2».SineContinuum.T_X`,
`«2610.05164v2».SineContinuum.reflect_mem`, `«2610.05164v2».SineContinuum.T_mem` with the
arguments shown in the proof.
-/
theorem T_reflect (x : ℝ) : T (-x)=1-T x := by
  have ht := T_X (reflect_mem (T_mem x))
  rw [X_reflect,X_T] at ht
  exact ht

end
end «2610.05164v2».SineContinuum
