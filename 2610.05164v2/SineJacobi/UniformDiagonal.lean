import «2610.05164v2».SineJacobi.ArticleChain
import «2610.05164v2».Finite.Gain
import «2606.16671v2».SineJacobi.ProfileBounds

/-!
Article: 2610.05164v2, Proposition 10.
Lemma 6, with the printed 64N constant and the actual inverse-matrix diagonal.
Result: `«2610.05164v2».SineJacobi.chain_green_diagonal_bound` supplies the stated article
conclusion.
-/
namespace «2610.05164v2».SineJacobi
noncomputable section
open Real «2606.16671v2».SineJacobi
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `«2606.16671v2».SineJacobi.greenWeight N s ≤ 64*(N:ℝ)`.

Use: `«2610.05164v2».SineJacobi.chain_green_diagonal_bound` uses this bound to establish the
stated quantitative bound `0 < (chain N).green i i ∧ (chain N).green i i ≤ 64*(N:ℝ)`.

Article: 2610.05164v2, Proposition 10 via
`«2610.05164v2».SineJacobi.chain_green_diagonal_bound`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.endpoint_half_bound`,
`«2606.16671v2».SineJacobi.endpoint_midpoint_control`, `«2606.16671v2».SineJacobi.endpoint_pos`
with the arguments shown in the proof.
-/
private theorem greenWeight_half_bound (N s : ℕ) (hN : 4 ≤ N) (hs : s < N) (hh : 2*s ≤ N) :
    «2606.16671v2».SineJacobi.greenWeight N s ≤ 64*(N:ℝ) := by
  -- Use the identities/estimates `«2606.16671v2».SineJacobi.endpoint_half_bound`,
  -- `«2606.16671v2».SineJacobi.endpoint_midpoint_control`,
  -- `«2606.16671v2».SineJacobi.endpoint_pos` with the arguments shown in the proof.
  let m := N/2
  have hm : m < N := by dsimp [m]; omega
  have hsm : s ≤ m := by dsimp [m]; omega
  have ha := endpoint_half_bound N s hs hh
  have hb := endpoint_midpoint_control N (N-s-1) (by omega) (by omega)
  have hc := endpoint_half_bound N m hm (by dsimp [m]; omega)
  have hroot : sqrt ((s:ℝ)+1) ≤ sqrt ((m:ℝ)+1) := by
    apply sqrt_le_sqrt
    exact_mod_cast Nat.add_le_add_right hsm 1
  have hf : endpoint N s ≤ (π^2/2)*sqrt ((m:ℝ)+1) :=
    ha.trans (mul_le_mul_of_nonneg_left hroot (by positivity))
  have hg : endpoint N (N-s-1) ≤ 3*((π^2/2)*sqrt ((m:ℝ)+1)) := by linarith
  have hp := mul_le_mul hf hg (endpoint_pos N (N-s-1) (by omega)).le (by positivity)
  have hmN : (m:ℝ)+1 ≤ 3*(N:ℝ)/4 := by
    have h := (show 4*(m+1) ≤ 3*N by dsimp [m]; omega)
    have hh : (4:ℝ)*((m:ℝ)+1) ≤ 3*(N:ℝ) := by exact_mod_cast h
    linarith
  have hpi : π^4 ≤ 100 := by
    calc
      _ ≤ (3.15:ℝ)^4 := pow_le_pow_left₀ pi_pos.le pi_lt_d2.le 4
      _ ≤ _ := by norm_num
  calc
    _ ≤ ((π^2/2)*sqrt ((m:ℝ)+1))*(3*((π^2/2)*sqrt ((m:ℝ)+1))) := hp
    _ = (3*π^4/4)*((m:ℝ)+1) := by
      have hr := sq_sqrt (show (0:ℝ) ≤ (m:ℝ)+1 by positivity)
      nlinarith [hr]
    _ ≤ (3*π^4/4)*(3*(N:ℝ)/4) := mul_le_mul_of_nonneg_left hmN (by positivity)
    _ ≤ 64*(N:ℝ) := by nlinarith [(show (0:ℝ) ≤ N from Nat.cast_nonneg N),mul_le_mul_of_nonneg_right hpi ((show (0:ℝ) ≤ N from Nat.cast_nonneg N))]

/--
Lemma 6, with the printed 64N constant and the actual inverse-matrix diagonal.

The stated quantitative bound `0 < (chain N).green i i ∧ (chain N).green i i ≤ 64*(N:ℝ)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Proposition 10.

Proof: Separate `4 ≤ N` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem chain_green_diagonal_bound (N : ℕ) (hN : 2 ≤ N) (i : Fin N) :
    0 < (chain N).green i i ∧ (chain N).green i i ≤ 64*(N:ℝ) := by
  -- Separate `4 ≤ N` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hn : 0 < N := by omega
  refine ⟨(chain N).green_diagonal_pos hn (terminal N hn) i,?_⟩
  by_cases h4 : 4 ≤ N
  · rw [chain_green_diagonal]
    by_cases hh : 2*i.val ≤ N
    · exact greenWeight_half_bound N i.val h4 i.isLt hh
    · have hr : 2*(N-i.val-1) ≤ N := by omega
      have hrev : «2606.16671v2».SineJacobi.greenWeight N i.val =
          «2606.16671v2».SineJacobi.greenWeight N (N-i.val-1) := by
        unfold «2606.16671v2».SineJacobi.greenWeight
        rw [show N-(N-i.val-1)-1 = i.val by omega,mul_comm]
      rw [hrev]
      exact greenWeight_half_bound N (N-i.val-1) h4 (by omega) hr
  · have hdiag := Finset.single_le_sum
      (f := fun j : Fin N => (chain N).green j j)
      (fun j _ => ((chain N).green_diagonal_pos hn (terminal N hn) j).le) (Finset.mem_univ i)
    change (chain N).green i i ≤ Matrix.trace (chain N).green at hdiag
    rw [(chain N).green_trace hn (terminal N hn)] at hdiag
    have hsmall : (N:ℝ) ≤ 3 := by exact_mod_cast (show N ≤ 3 by omega)
    nlinarith [(show (0:ℝ) ≤ N from Nat.cast_nonneg N)]

end
end «2610.05164v2».SineJacobi
