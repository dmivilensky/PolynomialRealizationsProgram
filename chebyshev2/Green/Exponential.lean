import chebyshev2.Green.Centered
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Fin.Basic

/-!
Article: chebyshev2, Proposition 1.
Lemma 3: factorization of every entry of the actual inverse matrix.
Use: `chebyshev2.Jacobi.green_exponential` feeds `chebyshev2.Jacobi.green_representation`
(The kernel representation in Proposition 1, for the original chain).
Proof chain: `chebyshev2.Packing.exists_representation` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace chebyshev2.Jacobi
noncomputable section
open Matrix Real
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
Green coordinates anchored at the first site.

Use: `chebyshev2.Jacobi.green_exponential` uses this definition to establish the identity
`J.green i j = sqrt (J.green i i*J.green j j)*exp (-|J.position hN i-J.position hN j|)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.
-/
def position (hN : 0 < N) (i : Fin N) : ℝ :=
  (1/2:ℝ)*log (J.green i i)-log (J.green ⟨0,hN⟩ i)+(1/2:ℝ)*log (J.green ⟨0,hN⟩ ⟨0,hN⟩)

/--
Exact identity `J.position hN ⟨0,hN⟩ = 0`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: chebyshev2, Proposition 1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
@[simp] theorem position_zero (hN : 0 < N) : J.position hN ⟨0,hN⟩ = 0 := by dsimp [position]; ring

/--
Exact identity `J.position hN j-J.position hN i = (1/2:ℝ)*log (J.green i i*J.green j j/J.green
i j^2)`.

Use: `chebyshev2.Jacobi.green_exponential_of_le` uses this identity to establish exact
identity `J.green i j = sqrt (J.green i i*J.green j j)*exp (J.position hN i-J.position hN j)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.green_entry_pos`,
`chebyshev2.Jacobi.green_markov` with the arguments shown in the proof.
-/
theorem position_difference (hN : 0 < N) (hm : (1-J.matrix).PosDef)
    (hir : J.Irreducible) (i j : Fin N) (hij : i.val ≤ j.val) :
    J.position hN j-J.position hN i =
      (1/2:ℝ)*log (J.green i i*J.green j j/J.green i j^2) := by
  -- Use the identities/estimates `chebyshev2.Jacobi.green_entry_pos`,
  -- `chebyshev2.Jacobi.green_markov` with the arguments shown in the proof.
  have hi := J.green_entry_pos hm hir i i
  have hj := J.green_entry_pos hm hir j j
  have hf := J.green_entry_pos hm hir i j
  have hi0 := J.green_entry_pos hm hir ⟨0,hN⟩ i
  have hj0 := J.green_entry_pos hm hir ⟨0,hN⟩ j
  have he := congrArg log (J.green_markov hm ⟨0,hN⟩ i j (by simp) hij)
  rw [log_mul hj0.ne' hi.ne', log_mul hi0.ne' hf.ne'] at he
  rw [log_div (mul_pos hi hj).ne' (pow_ne_zero 2 hf.ne'), log_mul hi.ne' hj.ne', log_pow]
  dsimp [position]
  linarith

/--
The spacing formula in Lemma 3.

Exact identity `J.position hN j-J.position hN i = (1/2:ℝ)*log (1+1/J.edgeFlow i)`.

Use: `chebyshev2.Jacobi.position_strictMono` uses this identity to establish the precise
assertion is `StrictMono (J.position hN)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.position_difference`,
`chebyshev2.Jacobi.green_neighbor_ratio` with the arguments shown in the proof.
-/
theorem position_spacing (hN : 0 < N) (hm : (1-J.matrix).PosDef)
    (hc : ∀ i < N, J.data.b i = 0) (hir : J.Irreducible)
    (i j : Fin N) (hij : i.val+1 = j.val) :
    J.position hN j-J.position hN i = (1/2:ℝ)*log (1+1/J.edgeFlow i) := by rw [J.position_difference hN hm hir i j (by omega), J.green_neighbor_ratio hm hc hir i j hij]

/--
The precise assertion is `StrictMono (J.position hN)`.

Use: `chebyshev2.Jacobi.green_exponential` uses this assertion to establish the identity
`J.green i j = sqrt (J.green i i*J.green j j)*exp (-|J.position hN i-J.position hN j|)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.position_spacing`,
`chebyshev2.Jacobi.edgeFlow_pos` with the arguments shown in the proof.
-/
theorem position_strictMono (hN : 0 < N) (hm : (1-J.matrix).PosDef)
    (hc : ∀ i < N, J.data.b i = 0) (hir : J.Irreducible) : StrictMono (J.position hN) := by
  -- Use the identities/estimates `chebyshev2.Jacobi.position_spacing`,
  -- `chebyshev2.Jacobi.edgeFlow_pos` with the arguments shown in the proof.
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have he := J.position_spacing hN hm hc hir i.castSucc i.succ (by simp)
  have hp := J.edgeFlow_pos hm hir i.castSucc (by simp)
  have hl : 0 < log (1+1/J.edgeFlow i.castSucc) := log_pos (by
    have := one_div_pos.mpr hp; linarith)
  linarith

/--
Exact identity `J.green i j = sqrt (J.green i i*J.green j j)*exp (J.position hN i-J.position hN
j)`.

Use: `chebyshev2.Jacobi.green_exponential` uses this identity to establish the identity
`J.green i j = sqrt (J.green i i*J.green j j)*exp (-|J.position hN i-J.position hN j|)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.green_entry_pos`,
`chebyshev2.Jacobi.position_difference` with the arguments shown in the proof.
-/
theorem green_exponential_of_le (hN : 0 < N) (hm : (1-J.matrix).PosDef)
    (hir : J.Irreducible) (i j : Fin N) (hij : i.val ≤ j.val) :
    J.green i j = sqrt (J.green i i*J.green j j)*exp (J.position hN i-J.position hN j) := by
  -- Use the identities/estimates `chebyshev2.Jacobi.green_entry_pos`,
  -- `chebyshev2.Jacobi.position_difference` with the arguments shown in the proof.
  have hi := J.green_entry_pos hm hir i i
  have hj := J.green_entry_pos hm hir j j
  have hf := J.green_entry_pos hm hir i j
  have hd := mul_pos hi hj
  have he := J.position_difference hN hm hir i j hij
  rw [log_div hd.ne' (pow_ne_zero 2 hf.ne'), log_pow] at he
  have hlog : log (J.green i j) =
      log (sqrt (J.green i i*J.green j j)*exp (J.position hN i-J.position hN j)) := by
    rw [log_mul (sqrt_pos.mpr hd).ne' (exp_pos _).ne', log_sqrt hd.le, log_exp]
    linarith
  have hh := congrArg exp hlog
  simpa only [exp_log hf, exp_log (mul_pos (sqrt_pos.mpr hd) (exp_pos _))] using hh

/--
Lemma 3: factorization of every entry of the actual inverse matrix.

Exact identity `J.green i j = sqrt (J.green i i*J.green j j)*exp (-|J.position hN i-J.position
hN j|)`.

Use: `chebyshev2.Jacobi.green_representation` uses this identity to establish exact
identity `J.green i j = sqrt (J.green i i*J.green j j)* exp (-|J.representationPoint hN
i-J.representationPoint hN j|)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Separate `i.val ≤ j.val` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem green_exponential (hN : 0 < N) (hm : (1-J.matrix).PosDef)
    (hc : ∀ i < N, J.data.b i = 0) (hir : J.Irreducible) (i j : Fin N) :
    J.green i j = sqrt (J.green i i*J.green j j)*exp (-|J.position hN i-J.position hN j|) := by
  -- Separate `i.val ≤ j.val` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  have hm' := (J.position_strictMono hN hm hc hir).monotone
  by_cases hij : i.val ≤ j.val
  · have he := J.green_exponential_of_le hN hm hir i j hij
    have hp : J.position hN i ≤ J.position hN j := hm' hij
    simpa [abs_of_nonpos (sub_nonpos.mpr hp)] using he
  · rw [J.green_symmetric hm j i, mul_comm (J.green i i), abs_sub_comm]
    have hji : j.val ≤ i.val := by omega
    have he := J.green_exponential_of_le hN hm hir j i hji
    have hp : J.position hN j ≤ J.position hN i := hm' hji
    simpa [abs_of_nonpos (sub_nonpos.mpr hp)] using he

end
end chebyshev2.Jacobi
