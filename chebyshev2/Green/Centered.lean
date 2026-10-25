import chebyshev2.Green.Markov

/-!
Article: chebyshev2, Proposition 1.
The adjacent Green minor identity, derived from the inverse equations.
Use: `chebyshev2.Jacobi.green_neighbor_ratio` feeds `chebyshev2.Jacobi.position_spacing`
(The spacing formula in Lemma 3).
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
Defines `edgeFlow` of type `ℝ` by `if h : i.val+1 < N then sqrt (J.data.aSq (i.val+1))*J.green
i ⟨i.val+1,h⟩ else 0`.

Use: `chebyshev2.Jacobi.centered_green_diagonal` uses this definition to establish exact
identity `J.green i i = 1+J.incomingFlow i+J.edgeFlow i`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.
-/
def edgeFlow (i : Fin N) : ℝ := if h : i.val+1 < N then
  sqrt (J.data.aSq (i.val+1))*J.green i ⟨i.val+1,h⟩ else 0

/--
Defines `incomingFlow` of type `ℝ` by `if h : 0 < i.val then sqrt (J.data.aSq i.val)*J.green
⟨i.val-1,by omega⟩ i else 0`.

Use: `chebyshev2.Jacobi.centered_green_diagonal` uses this definition to establish exact
identity `J.green i i = 1+J.incomingFlow i+J.edgeFlow i`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.
-/
def incomingFlow (i : Fin N) : ℝ := if h : 0 < i.val then
  sqrt (J.data.aSq i.val)*J.green ⟨i.val-1,by omega⟩ i else 0

/--
The stated quantitative bound `0 < J.edgeFlow i`.

Use: `chebyshev2.Jacobi.lift_interval_room` uses this bound to establish the stated
quantitative bound `1/J.green i i ≤ J.lift.position (by omega) ⟨2*i.val+1,by omega⟩ -
J.lift.position (by omega) ⟨2*i.val-1,by omega⟩`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.green_entry_pos` with the arguments
shown in the proof.
-/
theorem edgeFlow_pos (hm : (1-J.matrix).PosDef) (hir : J.Irreducible)
    (i : Fin N) (hi : i.val+1 < N) : 0 < J.edgeFlow i := by
  rw [edgeFlow, dite_eq_left hi]
  exact mul_pos (sqrt_pos.mpr (hir _ (by omega) hi)) (J.green_entry_pos hm hir _ _)

/--
The balance d_i=1+t_{i-1}+t_i of Lemma 3.

Exact identity `J.green i i = 1+J.incomingFlow i+J.edgeFlow i`.

Use: `chebyshev2.Jacobi.lift_interval_room` uses this identity to establish the stated
quantitative bound `1/J.green i i ≤ J.lift.position (by omega) ⟨2*i.val+1,by omega⟩ -
J.lift.position (by omega) ⟨2*i.val-1,by omega⟩`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Use the identities/estimates `chebyshev2.Jacobi.green_row`,
`chebyshev2.Jacobi.green_symmetric` with the arguments shown in the proof.
-/
theorem centered_green_diagonal (hm : (1-J.matrix).PosDef)
    (hc : ∀ i < N, J.data.b i = 0) (i : Fin N) :
    J.green i i = 1+J.incomingFlow i+J.edgeFlow i := by
  -- Use the identities/estimates `chebyshev2.Jacobi.green_row`,
  -- `chebyshev2.Jacobi.green_symmetric` with the arguments shown in the proof.
  have he := J.green_row hm i i
  simp only [hc i.val i.isLt, sub_zero, one_mul, ite_true] at he
  have hr : (if h : i.val+1 < N then
      sqrt (J.data.aSq (i.val+1))*J.green ⟨i.val+1,h⟩ i else 0) = J.edgeFlow i := by
    dsimp [edgeFlow]; split_ifs <;> first | rw [J.green_symmetric hm] | rfl
  rw [hr] at he
  change J.green i i-J.incomingFlow i-J.edgeFlow i = 1 at he
  linarith

/--
The adjacent Green minor identity, derived from the inverse equations.

Exact identity `sqrt (J.data.aSq j.val)*(J.green i i*J.green j j-J.green i j^2) = J.green i j`.

Use: `chebyshev2.Jacobi.green_neighbor_ratio` uses this identity to establish exact
identity `J.green i i*J.green j j/J.green i j^2 = 1+1/J.edgeFlow i`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Separate `0 < i.val` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem green_neighbor_minor (hm : (1-J.matrix).PosDef)
    (hc : ∀ i < N, J.data.b i = 0) (i j : Fin N) (hij : i.val+1 = j.val) :
    sqrt (J.data.aSq j.val)*(J.green i i*J.green j j-J.green i j^2) = J.green i j := by
  -- Separate `0 < i.val` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  have hn : i.val+1 < N := by omega
  have hj : (⟨i.val+1,hn⟩ : Fin N) = j := Fin.ext hij
  have hne : i ≠ j := by intro he; have hh := congrArg Fin.val he; omega
  have hd := J.green_row hm i i
  have hs := J.green_row hm i j
  simp only [hc i.val i.isLt, sub_zero, one_mul, hn, dite_true,
    ite_true, hne, ite_false] at hd hs
  rw [hj, hij] at hd hs
  rw [J.green_symmetric hm i j] at hd
  by_cases hi : 0 < i.val
  · simp only [hi, dite_true] at hd hs
    let p : Fin N := ⟨i.val-1,by omega⟩
    have hm' := J.green_markov hm p i j (by dsimp [p]; omega) (by omega)
    linear_combination J.green i j*hd-J.green i i*hs-sqrt (J.data.aSq i.val)*hm'
  · simp only [hi, dite_false, sub_zero] at hd hs
    linear_combination J.green i j*hd-J.green i i*hs

/--
Exact identity `J.green i i*J.green j j/J.green i j^2 = 1+1/J.edgeFlow i`.

Use: `chebyshev2.Jacobi.position_spacing` rewrites with this identity to establish exact
identity `J.position hN j-J.position hN i = (1/2:ℝ)*log (1+1/J.edgeFlow i)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.exists_representation`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem green_neighbor_ratio (hm : (1-J.matrix).PosDef)
    (hc : ∀ i < N, J.data.b i = 0) (hir : J.Irreducible)
    (i j : Fin N) (hij : i.val+1 = j.val) :
    J.green i i*J.green j j/J.green i j^2 = 1+1/J.edgeFlow i := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hp := J.green_entry_pos hm hir i j
  have hn : i.val+1 < N := by omega
  have hj : (⟨i.val+1,hn⟩ : Fin N) = j := Fin.ext hij
  have he := J.green_neighbor_minor hm hc i j hij
  have hcpl := sqrt_pos.mpr (hir j.val (by omega) j.isLt)
  rw [edgeFlow, dite_eq_left hn, hj, hij]
  field_simp [hp.ne', hcpl.ne']
  linear_combination he

end
end chebyshev2.Jacobi
