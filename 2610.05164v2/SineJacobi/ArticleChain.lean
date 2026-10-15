import «2610.05164v2».SineJacobi.Finite

/-!
Article: 2610.05164v2, Proposition 10.
D_N(t) is exactly the actual Green diagonal divided by N on each paper cell.
Use: `«2610.05164v2».SineJacobi.chain_green_diagonal` feeds
`«2610.05164v2».SineJacobi.diagonalProfile_cell` (D_N(t) is exactly the actual Green diagonal
divided by N on each paper cell).
Proof chain: `«2610.05164v2».SineJacobi.chain_green_diagonal_bound` — 2610.05164v2, Proposition 10;
Exact sine-energy integral, finite sums and truncation/convergence bounds.
-/
namespace «2610.05164v2».SineJacobi
noncomputable section
open «2606.16671v2» Matrix Real
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(chain N).matrix i i = 0`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 10.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.matrix_apply` with the arguments
shown in the proof.
-/
theorem chain_diagonal (N : ℕ) (i : Fin N) : (chain N).matrix i i = 0 := by simp [Jacobi.matrix, chain, JacobiData.matrix_apply]

/--
The displayed off-diagonal formula in Theorem 2.5.

Exact identity `(chain N).matrix i j = sin ((j:ℝ)*Real.pi/(N:ℝ))/ (2*sqrt (sin
(((j:ℝ)-1/2)*Real.pi/(N:ℝ))*sin (((j:ℝ)+1/2)*Real.pi/(N:ℝ))))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 10.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.sin_integer_pos`,
`«2606.16671v2».JacobiData.matrix_apply`, `«2606.16671v2».SineJacobi.data_aSq` with the
arguments shown in the proof.
-/
theorem chain_offdiagonal (N : ℕ) (i j : Fin N) (hij : i.val+1 = j.val) :
    (chain N).matrix i j = sin ((j:ℝ)*Real.pi/(N:ℝ))/
      (2*sqrt (sin (((j:ℝ)-1/2)*Real.pi/(N:ℝ))*sin (((j:ℝ)+1/2)*Real.pi/(N:ℝ)))) := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.sin_integer_pos`,
  -- `«2606.16671v2».JacobiData.matrix_apply`, `«2606.16671v2».SineJacobi.data_aSq` with the
  -- arguments shown in the proof.
  have hne : i ≠ j := by intro he; have hh := congrArg Fin.val he; omega
  have hj : 0 < j.val := by omega
  have hs := «2606.16671v2».SineJacobi.sin_integer_pos N j.val hj j.isLt
  simp only [Jacobi.matrix, chain, JacobiData.matrix_apply, Nat.zero_add, hne, ite_false,
    hij, ite_true]
  rw [«2606.16671v2».SineJacobi.data_aSq N j.val hj j.isLt, «2606.16671v2».SineJacobi.couplingSq,
    sqrt_div (by positivity), sqrt_mul (by norm_num : (0:ℝ) ≤ 1/4), sqrt_sq hs.le]
  norm_num
  simp only [«2606.16671v2».SineJacobi.h, mul_div_assoc]
  ring

/--
Exact identity `(chain N).green i i = «2606.16671v2».SineJacobi.greenWeight N i.val`.

Use: `«2610.05164v2».SineJacobi.diagonalProfile_cell` rewrites with this identity to establish
exact identity `diagonalProfile N t = (chain N).green i i/(N:ℝ)`.

Article: 2610.05164v2, Proposition 10 via
`«2610.05164v2».SineJacobi.chain_green_diagonal_bound`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.resolvent_diagonal` with the
arguments shown in the proof.
-/
theorem chain_green_diagonal (N : ℕ) (i : Fin N) :
    (chain N).green i i = «2606.16671v2».SineJacobi.greenWeight N i.val :=
  «2606.16671v2».SineJacobi.resolvent_diagonal N i

/--
D_N(t) is exactly the actual Green diagonal divided by N on each paper cell.

Exact identity `diagonalProfile N t = (chain N).green i i/(N:ℝ)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 10.

Proof: Use the identities/estimates `«2610.05164v2».SineJacobi.chain_green_diagonal` with the
arguments shown in the proof.
-/
theorem diagonalProfile_cell (N : ℕ) (i : Fin N) (t : ℝ)
    (ht : t ∈ Set.Ico ((i:ℝ)/(N:ℝ)) (((i:ℝ)+1)/(N:ℝ))) :
    diagonalProfile N t = (chain N).green i i/(N:ℝ) := by
  -- Use the identities/estimates `«2610.05164v2».SineJacobi.chain_green_diagonal` with the
  -- arguments shown in the proof.
  have hn0 : 0 < N := by have := i.isLt; omega
  have hn : (0:ℝ) < N := by exact_mod_cast hn0
  have hl : (i:ℝ) ≤ (N:ℝ)*t := by
    have hh := (div_le_iff₀ hn).mp ht.1
    simpa [mul_comm] using hh
  have hu : (N:ℝ)*t < (i:ℝ)+1 := by
    have hh := (lt_div_iff₀ hn).mp ht.2
    simpa [mul_comm] using hh
  have hf : Nat.floor ((N:ℝ)*t) = i.val :=
    (Nat.floor_eq_iff ((Nat.cast_nonneg i.val).trans hl)).mpr ⟨hl,hu⟩
  rw [chain_green_diagonal]
  change «2606.16671v2».SineJacobi.greenWeight N (Nat.floor ((N:ℝ)*t))/(N:ℝ) = _
  rw [hf]

end
end «2610.05164v2».SineJacobi
