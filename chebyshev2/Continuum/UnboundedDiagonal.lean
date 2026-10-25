import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Article: chebyshev2, Lemma 5.
Equality with mathlib's true unbounded adjoint.
Use: `chebyshev2.Continuum.unboundedDiagonalOperator_selfAdjoint` feeds
`chebyshev2.SineContinuum.legendreOperator_selfAdjoint` (Self-adjointness uses mathlib's genuine
adjoint of an unbounded operator).
Proof chain: `chebyshev2.SineContinuum.standardLegendreOperator_selfAdjoint` — chebyshev2,
Lemma 5; Legendre operator, nonlogarithmic realization and continuum sine spectrum.
-/
namespace chebyshev2.Continuum
noncomputable section
open Set
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
A diagonal graph in an actual Hilbert space, with a prescribed complete Hilbert basis and
arbitrary real eigenvalues.

Use: `chebyshev2.Continuum.unboundedDiagonalDomain` uses this definition in the displayed
construction of `unboundedDiagonalDomain`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def UnboundedDiagonalGraph (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ) (u v : E) : Prop :=
  ∀ n, b.repr v n=w n*b.repr u n

namespace UnboundedDiagonalGraph
variable {b : HilbertBasis ℕ ℝ E} {w : ℕ → ℝ} {u v v' : E}
/--
Exact identity `v=v'`.

Use: `chebyshev2.Continuum.unboundedDiagonalOperator_basis` uses this identity to establish
exact identity `unboundedDiagonalOperator b w ⟨b j,unboundedDiagonalDomain_basis b w j⟩=w j • b
j`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_operator`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem unique (h : UnboundedDiagonalGraph b w u v) (h' : UnboundedDiagonalGraph b w u v') : v=v' := by
  apply b.repr.injective
  ext n
  exact (h n).trans (h' n).symm
end UnboundedDiagonalGraph

/--
Constructs `unboundedDiagonalDomain` of type `Submodule ℝ E` by the displayed record fields.
Data fields specify the construction; proof fields discharge its required properties.

Use: `chebyshev2.Continuum.unboundedDiagonalDomain_dense` uses this definition to establish
the precise assertion is `Dense (unboundedDiagonalDomain b w : Set E)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def unboundedDiagonalDomain (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ) : Submodule ℝ E where
  carrier := {u | ∃ v, UnboundedDiagonalGraph b w u v}
  zero_mem' := ⟨0,by intro n; simp⟩
  add_mem' := by
    rintro u v ⟨u',hu⟩ ⟨v',hv⟩
    refine ⟨u'+v',?_⟩
    intro n
    simp only [map_add,lp.coeFn_add, Pi.add_apply]
    rw [hu n,hv n,mul_add]
  smul_mem' := by
    rintro c u ⟨v,hv⟩
    refine ⟨c • v,?_⟩
    intro n
    simp only [map_smul,lp.coeFn_smul, Pi.smul_apply,smul_eq_mul]
    rw [hv n]
    ring

/--
Defines `unboundedDiagonalValue` of type `E` by `Classical.choose u.property`.

Use: `chebyshev2.Continuum.unboundedDiagonalOperator` uses this definition in the displayed
construction of `unboundedDiagonalOperator`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def unboundedDiagonalValue (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ) (u : unboundedDiagonalDomain b w) : E :=
  Classical.choose u.property

/--
The precise assertion is `UnboundedDiagonalGraph b w u (unboundedDiagonalValue b w u)`.

Use: `chebyshev2.Continuum.unboundedDiagonalOperator_graph` uses this assertion to
establish the precise assertion is `UnboundedDiagonalGraph b w u (unboundedDiagonalOperator b w
u)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem unboundedDiagonalValue_graph (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ) (u : unboundedDiagonalDomain b w) :
    UnboundedDiagonalGraph b w u (unboundedDiagonalValue b w u) := Classical.choose_spec u.property

/--
The literal unbounded diagonal operator, as a partially defined linear map.

Use: `chebyshev2.Continuum.unboundedDiagonalOperator_nonnegative` rewrites with this
definition to prove the bound `0 ≤ inner ℝ (unboundedDiagonalOperator b
w u) (u:E)`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.
-/
def unboundedDiagonalOperator (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ) : E →ₗ.[ℝ] E where
  domain := unboundedDiagonalDomain b w
  toFun := {
    toFun := unboundedDiagonalValue b w
    map_add' := by
      intro u v
      apply UnboundedDiagonalGraph.unique (unboundedDiagonalValue_graph b w (u+v))
      intro n
      change b.repr (unboundedDiagonalValue b w u+unboundedDiagonalValue b w v) n = w n*b.repr ((u:E)+(v:E)) n
      simp only [map_add,lp.coeFn_add, Pi.add_apply]
      rw [unboundedDiagonalValue_graph b w u n,unboundedDiagonalValue_graph b w v n,mul_add]
    map_smul' := by
      intro c u
      apply UnboundedDiagonalGraph.unique (unboundedDiagonalValue_graph b w (c • u))
      intro n
      change b.repr (c • unboundedDiagonalValue b w u) n = w n*b.repr (c • (u:E)) n
      simp only [map_smul,lp.coeFn_smul, Pi.smul_apply,smul_eq_mul]
      rw [unboundedDiagonalValue_graph b w u n]
      ring }

/--
The precise assertion is `UnboundedDiagonalGraph b w u (unboundedDiagonalOperator b w u)`.

Use: `chebyshev2.Continuum.unboundedDiagonalOperator_basis` uses this assertion to
establish exact identity `unboundedDiagonalOperator b w ⟨b j,unboundedDiagonalDomain_basis b w
j⟩=w j • b j`.

Article: chebyshev2, Lemma 5 via `chebyshev2.SineContinuum.legendreV_domain`.

Proof: Use the identities/estimates `chebyshev2.Continuum.unboundedDiagonalValue_graph`
with the arguments shown in the proof.
-/
theorem unboundedDiagonalOperator_graph (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ)
    (u : (unboundedDiagonalOperator b w).domain) :
    UnboundedDiagonalGraph b w u (unboundedDiagonalOperator b w u) := unboundedDiagonalValue_graph b w u

/--
Equivalence of the displayed criteria: `u ∈ unboundedDiagonalDomain b w ↔ Summable (fun n => (w
n)^2*(b.repr u n)^2)`.

Use: `chebyshev2.SineContinuum.legendreOperator_domain` uses this identity to establish
equivalence of the displayed criteria: `u ∈ legendreOperator.domain ↔ Summable (fun n : ℕ =>
(n:ℝ)^2*((n:ℝ)+1)^2*(legendreHilbertBasis.repr u n)^2)`.

Article: chebyshev2, Lemma 5.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem unboundedDiagonalDomain_iff (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ) (u : E) :
    u ∈ unboundedDiagonalDomain b w ↔ Summable (fun n => (w n)^2*(b.repr u n)^2) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have he : Memℓp (fun n => w n*b.repr u n) 2 ↔
      Summable (fun n => (w n)^2*(b.repr u n)^2) := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
    simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,mul_pow]
  constructor
  · rintro ⟨v,hv⟩
    apply he.mp
    have hf : (fun n => w n*b.repr u n)=(fun n => b.repr v n) := funext (fun n => (hv n).symm)
    rw [hf]
    exact lp.memℓp (b.repr v)
  · intro h
    let v : lp (fun _ : ℕ => ℝ) 2 := ⟨fun n => w n*b.repr u n,he.mpr h⟩
    refine ⟨b.repr.symm v,?_⟩
    intro n
    rw [b.repr.apply_symm_apply]

/--
Membership in the specified domain/enclosure: `b j ∈ unboundedDiagonalDomain b w`.

Use: `chebyshev2.Continuum.unboundedDiagonalDomain_dense` uses this assertion to establish
the precise assertion is `Dense (unboundedDiagonalDomain b w : Set E)`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.standardLegendreOperator_selfAdjoint`.

Proof: Separate `n=j` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem unboundedDiagonalDomain_basis (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ) (j : ℕ) :
    b j ∈ unboundedDiagonalDomain b w := by
  -- Separate `n=j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  refine ⟨w j • b j,?_⟩
  intro n
  classical
  simp only [map_smul,lp.coeFn_smul, Pi.smul_apply,smul_eq_mul,b.repr_self,lp.single_apply]
  by_cases hn : n=j
  · subst n; simp
  · simp [hn]

/--
Exact identity `unboundedDiagonalOperator b w ⟨b j,unboundedDiagonalDomain_basis b w j⟩=w j • b
j`.

Use: `chebyshev2.Continuum.unboundedDiagonalOperator_selfAdjoint` rewrites with this
identity to establish the identity `(unboundedDiagonalOperator b
w).adjoint=unboundedDiagonalOperator b w`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.standardLegendreOperator_selfAdjoint`.

Proof: Separate `n=j` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem unboundedDiagonalOperator_basis (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ) (j : ℕ) :
    unboundedDiagonalOperator b w ⟨b j,unboundedDiagonalDomain_basis b w j⟩=w j • b j := by
  -- Separate `n=j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply UnboundedDiagonalGraph.unique (unboundedDiagonalOperator_graph b w _)
  intro n
  classical
  simp only [map_smul,lp.coeFn_smul, Pi.smul_apply,smul_eq_mul,b.repr_self,lp.single_apply]
  by_cases hn : n=j
  · subst n; simp
  · simp [hn]

/--
The precise assertion is `Dense (unboundedDiagonalDomain b w : Set E)`.

Use: `chebyshev2.Continuum.unboundedDiagonalOperator_selfAdjoint` uses this assertion to
establish exact identity `(unboundedDiagonalOperator b w).adjoint=unboundedDiagonalOperator b
w`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.standardLegendreOperator_selfAdjoint`.

Proof: Use the identities/estimates `chebyshev2.Continuum.unboundedDiagonalDomain_basis`
with the arguments shown in the proof.
-/
theorem unboundedDiagonalDomain_dense (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ) :
    Dense (unboundedDiagonalDomain b w : Set E) := by
  -- Use the identities/estimates `chebyshev2.Continuum.unboundedDiagonalDomain_basis` with
  -- the arguments shown in the proof.
  have hs : Submodule.span ℝ (range b) ≤ unboundedDiagonalDomain b w :=
    Submodule.span_le.mpr (by rintro _ ⟨n,rfl⟩; exact unboundedDiagonalDomain_basis b w n)
  have ht := Submodule.topologicalClosure_mono hs
  rw [b.dense_span] at ht
  have he : (unboundedDiagonalDomain b w).topologicalClosure=⊤ := top_unique ht
  rw [dense_iff_closure_eq,← Submodule.topologicalClosure_coe,he]
  rfl

/--
The precise assertion is `(unboundedDiagonalOperator b w).IsFormalAdjoint
(unboundedDiagonalOperator b w)`.

Use: `chebyshev2.Continuum.unboundedDiagonalOperator_selfAdjoint` uses this assertion to
establish exact identity `(unboundedDiagonalOperator b w).adjoint=unboundedDiagonalOperator b
w`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.standardLegendreOperator_selfAdjoint`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem unboundedDiagonalOperator_symmetric (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ) :
    (unboundedDiagonalOperator b w).IsFormalAdjoint (unboundedDiagonalOperator b w) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  intro u v
  rw [← b.tsum_inner_mul_inner,← b.tsum_inner_mul_inner]
  apply tsum_congr
  intro n
  have hu := unboundedDiagonalOperator_graph b w u n
  have hv := unboundedDiagonalOperator_graph b w v n
  simp only [b.repr_apply_apply] at hu hv
  rw [real_inner_comm (b n) (unboundedDiagonalOperator b w u),hu,hv]
  rw [real_inner_comm (b n) (u:E)]
  ring

variable [CompleteSpace E]

/--
Equality with mathlib's true unbounded adjoint. The full weighted-square summability domain is
essential to this assertion.

Exact identity `(unboundedDiagonalOperator b w).adjoint=unboundedDiagonalOperator b w`.

Use: `chebyshev2.SineContinuum.legendreOperator_selfAdjoint` uses this identity to
establish exact identity `legendreOperator.adjoint=legendreOperator`.

Article: chebyshev2, Lemma 5 via
`chebyshev2.SineContinuum.standardLegendreOperator_selfAdjoint`.

Proof: Use the identities/estimates `chebyshev2.Continuum.unboundedDiagonalDomain_dense`,
`chebyshev2.Continuum.unboundedDiagonalDomain_basis`,
`chebyshev2.Continuum.unboundedDiagonalOperator_basis` with the arguments shown in the
proof.
-/
theorem unboundedDiagonalOperator_selfAdjoint (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ) :
    (unboundedDiagonalOperator b w).adjoint=unboundedDiagonalOperator b w := by
  -- Use the identities/estimates `chebyshev2.Continuum.unboundedDiagonalDomain_dense`,
  -- `chebyshev2.Continuum.unboundedDiagonalDomain_basis`,
  -- `chebyshev2.Continuum.unboundedDiagonalOperator_basis` with the arguments shown in the
  -- proof.
  let A := unboundedDiagonalOperator b w
  have hd : Dense (A.domain : Set E) := unboundedDiagonalDomain_dense b w
  have hf := A.adjoint_isFormalAdjoint hd
  apply le_antisymm
  · refine ⟨?_,?_⟩
    · intro u hu
      refine ⟨A.adjoint ⟨u,hu⟩,?_⟩
      intro n
      have h := hf ⟨u,hu⟩ ⟨b n,unboundedDiagonalDomain_basis b w n⟩
      rw [unboundedDiagonalOperator_basis] at h
      simpa only [b.repr_apply_apply,real_inner_smul_right,real_inner_comm] using h
    · intro u v huv
      symm
      apply UnboundedDiagonalGraph.unique (unboundedDiagonalOperator_graph b w v)
      intro n
      have h := hf u ⟨b n,unboundedDiagonalDomain_basis b w n⟩
      rw [unboundedDiagonalOperator_basis] at h
      rw [← huv]
      simpa only [b.repr_apply_apply,real_inner_smul_right,real_inner_comm] using h
  · exact (unboundedDiagonalOperator_symmetric b w).le_adjoint hd

omit [CompleteSpace E] in
/--
The stated quantitative bound `0 ≤ inner ℝ (unboundedDiagonalOperator b w u) (u:E)`.

Use: `chebyshev2.SineContinuum.legendreOperator_nonnegative` uses this bound to establish
the stated quantitative bound `0 ≤ inner ℝ (legendreOperator u) (u:LegendreSpace)`.

Article: chebyshev2, Lemma 5.

Proof: Use the identities/estimates `chebyshev2.Continuum.unboundedDiagonalOperator_graph`
with the arguments shown in the proof.
-/
theorem unboundedDiagonalOperator_nonnegative (b : HilbertBasis ℕ ℝ E) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (u : (unboundedDiagonalOperator b w).domain) :
    0 ≤ inner ℝ (unboundedDiagonalOperator b w u) (u:E) := by
  -- Use the identities/estimates `chebyshev2.Continuum.unboundedDiagonalOperator_graph`
  -- with the arguments shown in the proof.
  rw [← b.tsum_inner_mul_inner]
  apply tsum_nonneg
  intro n
  have h := unboundedDiagonalOperator_graph b w u n
  simp only [b.repr_apply_apply] at h
  rw [real_inner_comm (b n) (unboundedDiagonalOperator b w u),h]
  simpa only [mul_assoc,← pow_two] using mul_nonneg (hw n) (sq_nonneg (inner ℝ (b n) (u:E)))

end
end chebyshev2.Continuum
