import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
Article: 2610.05164v2, Lemma 25.
Lemma 25: chord-Newton contraction, including automatic nonsingularity of the preconditioner and the
geometric error bound.
Use: `«2610.05164v2».Primal.chord_newton_matrix` feeds
`«2610.05164v2».Primal.exact_primal_family_of_contraction` (Theorem 5.2's analytic implication, for
any finite observation family).
Proof chain: `«2610.05164v2».Primal.exact_primal_family_of_contraction` — 2610.05164v2, Theorem 5.2;
Contraction implies exact feasible density, uniqueness, iteration error and energy bound.
Source: mathlib, Mathlib.Topology.MetricSpace.Contracting; Golub and Van Loan, Matrix Computations —
Banach fixed-point and preconditioned chord iteration. The needed form is proved here.
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set Metric Filter
open scoped Topology NNReal
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/--
Constructs witnesses with the exact properties `∃ a∈closedBall (0:E) ρ,F a=0 ∧ Tendsto (fun n
=> (fun x => x-C (F x))^[n] 0) atTop (𝓝 a) ∧ ∀ b∈closedBall (0:E) ρ,F b=0 → b=a`.

Use: `«2610.05164v2».Primal.chord_newton_matrix` uses this identity to establish the identity
stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via
`«2610.05164v2».Primal.exact_primal_family_of_contraction`.

Source: mathlib, Mathlib.Topology.MetricSpace.Contracting; Golub and Van Loan, Matrix
Computations — Banach fixed-point and preconditioned chord iteration.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem chord_newton {F : E → E} (C : E ≃L[ℝ] E) {ρ ε : ℝ} {K : ℝ≥0}
    (hρ : 0≤ρ) (hK : K<1) (h0 : ‖C (F 0)‖≤ε)
    (hLip : LipschitzOnWith K (fun x => x-C (F x)) (closedBall 0 ρ))
    (hbudget : ε+(K:ℝ)*ρ≤ρ) :
    ∃ a∈closedBall (0:E) ρ,F a=0 ∧
      Tendsto (fun n => (fun x => x-C (F x))^[n] 0) atTop (𝓝 a) ∧
      ∀ b∈closedBall (0:E) ρ,F b=0 → b=a := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  let N : E → E := fun x => x-C (F x)
  have hmem : (0:E)∈closedBall 0 ρ := by simpa using hρ
  have hmaps : MapsTo N (closedBall 0 ρ) (closedBall 0 ρ) := by
    intro x hx
    have hl := hLip.dist_le_mul x hx 0 hmem
    have hn : ‖N 0‖≤ε := by simpa [N] using h0
    have hx' : ‖x‖≤ρ := by simpa using hx
    have hnorm : ‖N x‖≤(K:ℝ)*ρ+ε := by
      calc
        ‖N x‖≤‖N x-N 0‖+‖N 0‖ := norm_le_norm_sub_add _ _
        _≤(K:ℝ)*‖x‖+ε := add_le_add (by simpa [dist_eq_norm,N] using hl) hn
        _≤(K:ℝ)*ρ+ε := by gcongr
    simpa using hnorm.trans (by linarith)
  have hc : ContractingWith K (hmaps.restrict N (closedBall 0 ρ) (closedBall 0 ρ)) := by
    refine ⟨hK,LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    exact hLip.dist_le_mul x.val x.property y.val y.property
  obtain ⟨a,ha,hfix,ht,_⟩ := hc.exists_fixedPoint' isClosed_closedBall.isComplete hmaps hmem
    (edist_ne_top _ _)
  have hzero : F a=0 := by
    apply C.injective
    rw [map_zero]
    have h : a-C (F a)=a := hfix
    exact sub_eq_self.mp h
  refine ⟨a,ha,hzero,ht,?_⟩
  intro b hb hFb
  have hfB : N b=b := by simp [N,hFb]
  have hl := hLip.dist_le_mul b hb a ha
  change dist (N b) (N a)≤(K:ℝ)*dist b a at hl
  rw [show N a=a from hfix,hfB] at hl
  apply dist_eq_zero.mp
  have hk : (K:ℝ)<1 := hK
  nlinarith [dist_nonneg (x := b) (y := a)]

/--
Constructs witnesses with the exact properties `∃ a∈closedBall (0:E) ρ,F a=0 ∧ Tendsto (fun n
=> (fun x => x-C (F x))^[n] 0) atTop (𝓝 a) ∧ ∀ b∈closedBall (0:E) ρ,F b=0 → b=a`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 25.

Source: mathlib, Mathlib.Topology.MetricSpace.Contracting; Golub and Van Loan, Matrix
Computations — Banach fixed-point and preconditioned chord iteration.

Proof: Use the identities/estimates `«2610.05164v2».Primal.chord_newton` with the arguments
shown in the proof.
-/
theorem chord_newton_of_derivative {F : E → E} (C : E ≃L[ℝ] E)
    (J : E → E →L[ℝ] E) {ρ ε : ℝ} {K : ℝ≥0}
    (hρ : 0≤ρ) (hK : K<1) (h0 : ‖C (F 0)‖≤ε)
    (hJ : ∀ x∈closedBall (0:E) ρ,HasFDerivAt F (J x) x)
    (hbound : ∀ x∈closedBall (0:E) ρ,
      ‖ContinuousLinearMap.id ℝ E-C.toContinuousLinearMap.comp (J x)‖≤(K:ℝ))
    (hbudget : ε+(K:ℝ)*ρ≤ρ) :
    ∃ a∈closedBall (0:E) ρ,F a=0 ∧
      Tendsto (fun n => (fun x => x-C (F x))^[n] 0) atTop (𝓝 a) ∧
      ∀ b∈closedBall (0:E) ρ,F b=0 → b=a := by
  -- Use the identities/estimates `«2610.05164v2».Primal.chord_newton` with the arguments shown
  -- in the proof.
  apply chord_newton C hρ hK h0 ?_ hbudget
  apply (convex_closedBall (0:E) ρ).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (f' := fun x => ContinuousLinearMap.id ℝ E-C.toContinuousLinearMap.comp (J x))
  · intro x hx
    exact ((hasFDerivAt_id x).sub (C.hasFDerivAt.comp x (hJ x hx))).hasFDerivWithinAt
  · intro x hx
    exact_mod_cast hbound x hx

/--
In finite dimension the paper's norm hypothesis already implies that the preconditioner is
invertible; invertibility is not an extra premise.

The precise assertion is `Function.Bijective C`.

Use: `«2610.05164v2».Primal.chord_newton_matrix` uses this assertion to establish the identity
stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via
`«2610.05164v2».Primal.exact_primal_family_of_contraction`.

Source: mathlib, Mathlib.Topology.MetricSpace.Contracting; Golub and Van Loan, Matrix
Computations — Banach fixed-point and preconditioned chord iteration.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem preconditioner_bijective [FiniteDimensional ℝ E] (C J : E →L[ℝ] E)
    (h : ‖ContinuousLinearMap.id ℝ E-C.comp J‖<1) : Function.Bijective C := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hu : IsUnit (C.comp J) := by
    have hh := isUnit_one_sub_of_norm_lt_one h
    simpa only [ContinuousLinearMap.one_def,sub_sub_cancel] using hh
  have hb := ContinuousLinearMap.isUnit_iff_bijective.mp hu
  have hs : Function.Surjective C := by
    intro y
    obtain ⟨x,hx⟩ := hb.2 y
    exact ⟨J x,hx⟩
  exact ⟨C.toLinearMap.injective_iff_surjective.mpr hs,hs⟩

omit [CompleteSpace E] in
/--
Establishes the uniform, quantified assertion `∀ n : ℕ,(fun x => x-C (F x))^[n] 0∈closedBall
(0:E) ρ ∧ ‖(fun x => x-C (F x))^[n] 0-a‖≤(K:ℝ)^n*ε/(1-K)`.

Use: `«2610.05164v2».Primal.chord_newton_matrix` uses this identity to establish the identity
stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via
`«2610.05164v2».Primal.exact_primal_family_of_contraction`.

Source: mathlib, Mathlib.Topology.MetricSpace.Contracting; Golub and Van Loan, Matrix
Computations — Banach fixed-point and preconditioned chord iteration.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem chord_iterate_error {F : E → E} (C : E ≃L[ℝ] E) {ρ ε : ℝ} {K : ℝ≥0}
    (hρ : 0≤ρ) (hK : K<1) (h0 : ‖C (F 0)‖≤ε)
    (hLip : LipschitzOnWith K (fun x => x-C (F x)) (closedBall 0 ρ))
    (hbudget : ε+(K:ℝ)*ρ≤ρ) {a : E} (ha : a∈closedBall (0:E) ρ) (hFa : F a=0) :
    ∀ n : ℕ,(fun x => x-C (F x))^[n] 0∈closedBall (0:E) ρ ∧
      ‖(fun x => x-C (F x))^[n] 0-a‖≤(K:ℝ)^n*ε/(1-K) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  let N : E → E := fun x => x-C (F x)
  have hz : (0:E)∈closedBall 0 ρ := by simpa using hρ
  have hNa : N a=a := by simp [N,hFa]
  have hN0 : ‖N 0‖≤ε := by simpa [N] using h0
  have hmaps : MapsTo N (closedBall 0 ρ) (closedBall 0 ρ) := by
    intro x hx
    have hnorm : ‖x‖≤ρ := by simpa using hx
    have hdist := hLip.dist_le_mul x hx 0 hz
    have hn : ‖N x‖≤‖N x-N 0‖+‖N 0‖ := norm_le_norm_sub_add _ _
    have hd : ‖N x-N 0‖≤(K:ℝ)*‖x‖ := by simpa only [dist_eq_norm,sub_zero] using hdist
    have hb := mul_le_mul_of_nonneg_left hnorm K.coe_nonneg
    have hh : ‖N x‖≤ρ := by linarith
    simpa using hh
  have hk : 0<(1-(K:ℝ)) := sub_pos.mpr hK
  have hstart : ‖a‖≤ε/(1-K) := by
    have hd := hLip.dist_le_mul a ha 0 hz
    change dist (N a) (N 0)≤(K:ℝ)*dist a 0 at hd
    rw [hNa,dist_eq_norm,dist_eq_norm,sub_zero] at hd
    have hn := norm_le_norm_sub_add a (N 0)
    apply (le_div_iff₀ hk).mpr
    nlinarith
  have herr : ∀ n : ℕ,‖N^[n] 0-a‖≤(K:ℝ)^n*‖a‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hd := hLip.dist_le_mul (N^[n] 0) (hmaps.iterate n hz) a ha
      change dist (N (N^[n] 0)) (N a)≤(K:ℝ)*dist (N^[n] 0) a at hd
      rw [hNa,dist_eq_norm,dist_eq_norm] at hd
      rw [Function.iterate_succ_apply']
      exact hd.trans (by simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using
        mul_le_mul_of_nonneg_left ih K.coe_nonneg)
  intro n
  refine ⟨hmaps.iterate n hz,(herr n).trans ?_⟩
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hstart (pow_nonneg K.coe_nonneg n)

/--
Lemma 25 in its finite-dimensional form with an arbitrary matrix C.

Use: `«2610.05164v2».Primal.exact_primal_family_of_contraction` uses this identity to establish
the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via
`«2610.05164v2».Primal.exact_primal_family_of_contraction`.

Source: mathlib, Mathlib.Topology.MetricSpace.Contracting; Golub and Van Loan, Matrix
Computations — Banach fixed-point and preconditioned chord iteration.

Proof: Use the identities/estimates `«2610.05164v2».Primal.preconditioner_bijective`,
`«2610.05164v2».Primal.chord_newton`, `«2610.05164v2».Primal.chord_iterate_error` with the
arguments shown in the proof.
-/
theorem chord_newton_matrix [FiniteDimensional ℝ E] {F : E → E} (C : E →L[ℝ] E)
    (J : E → E →L[ℝ] E) {ρ ε : ℝ} {K : ℝ≥0}
    (hρ : 0≤ρ) (hK : K<1) (h0 : ‖C (F 0)‖≤ε)
    (hJ : ∀ x∈closedBall (0:E) ρ,HasFDerivAt F (J x) x)
    (hbound : ∀ x∈closedBall (0:E) ρ,
      ‖ContinuousLinearMap.id ℝ E-C.comp (J x)‖≤(K:ℝ))
    (hbudget : ε+(K:ℝ)*ρ≤ρ) :
    Function.Bijective C ∧ ∃ a∈closedBall (0:E) ρ,F a=0 ∧
      Tendsto (fun n => (fun x => x-C (F x))^[n] 0) atTop (𝓝 a) ∧
      (∀ b∈closedBall (0:E) ρ,F b=0 → b=a) ∧
      ∀ n : ℕ,(fun x => x-C (F x))^[n] 0∈closedBall (0:E) ρ ∧
        ‖(fun x => x-C (F x))^[n] 0-a‖≤(K:ℝ)^n*ε/(1-K) := by
  -- Use the identities/estimates `«2610.05164v2».Primal.preconditioner_bijective`,
  -- `«2610.05164v2».Primal.chord_newton`, `«2610.05164v2».Primal.chord_iterate_error` with the
  -- arguments shown in the proof.
  have hz : (0:E)∈closedBall 0 ρ := by simpa using hρ
  have hb := preconditioner_bijective C (J 0) ((hbound 0 hz).trans_lt hK)
  let CE := ContinuousLinearEquiv.ofBijective C
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hCE : CE.toContinuousLinearMap=C := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hLip : LipschitzOnWith K (fun x => x-CE (F x)) (closedBall 0 ρ) := by
    apply (convex_closedBall (0:E) ρ).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f':=fun x => ContinuousLinearMap.id ℝ E-C.comp (J x))
    · intro x hx
      simpa only [hCE,Pi.sub_def,Function.comp_def,id_eq] using
        ((hasFDerivAt_id x).sub (CE.hasFDerivAt.comp x (hJ x hx))).hasFDerivWithinAt
    · intro x hx
      exact_mod_cast hbound x hx
  have h0' : ‖CE (F 0)‖≤ε := h0
  obtain ⟨a,ha,hFa,ht,hunique⟩ := chord_newton CE hρ hK h0' hLip hbudget
  exact ⟨hb,a,ha,hFa,ht,hunique,chord_iterate_error CE hρ hK h0' hLip hbudget ha hFa⟩

end
end «2610.05164v2».Primal
