import bezout.Balanced.Startup
import bezout.Balanced.Readout

/-!
Article: bezout, Algorithm 2 scalar preparation.
Use: a recursive scalar table computes the exact physical impulse entries from
the printed startup coefficients, and two reverse accumulators compute readout.
Proof: induction on the row index compares the scalar recursion with the actual
history's proved fourth-order impulse identity, including every startup row.
-/

namespace bezout.Algorithms.Balanced
noncomputable section

open Polynomial Polynomial.Chebyshev

/-- The printed scalar first-kind Chebyshev value preparation. -/
def preparedC (I : chebyshev1.SpectralInterval) : ℕ → ℝ
  | 0 => 1
  | 1 => I.eta
  | j+2 => 2*I.eta*preparedC I (j+1)-preparedC I j

/-- The recursive C table gives the exact exterior Chebyshev values. -/
theorem preparedC_eq (I : chebyshev1.SpectralInterval) (j : ℕ) :
    preparedC I j = (T ℝ (j:ℤ)).eval I.eta := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    match j with
    | 0 => simp [preparedC]
    | 1 => simp [preparedC]
    | j+2 =>
      have hr := congrArg (fun p : ℝ[X] => p.eval I.eta) (T_add_two ℝ (j:ℤ))
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at hr
      rw [preparedC, ih (j+1) (by omega), ih j (by omega)]
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hr.symm

/-- The printed scalar Z table, prepared separately in each degree parity. -/
def preparedNormalizer (I : chebyshev1.SpectralInterval) (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => I.eta
  | j+2 => preparedNormalizer I N j + bezout.Balanced.omega N (j+2) *
      (preparedC I (j+2)-preparedC I j)

/-- Recursive parity preparation gives every exact positive normalizer. -/
theorem preparedNormalizer_eq (I : chebyshev1.SpectralInterval) (N j : ℕ) :
    preparedNormalizer I N j = bezout.Balanced.normalizer I N j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    match j with
    | 0 => simp [preparedNormalizer]
    | 1 => simp [preparedNormalizer]
    | j+2 =>
      rw [preparedNormalizer, ih j (by omega), preparedC_eq, preparedC_eq]
      exact (bezout.Balanced.normalizer_add_two I N j).symm

/-- The two actual reverse accumulators, stepping backwards within one parity.
Use: the first update computes P; the second uses that newly updated P. -/
def preparedReverse (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ × ℝ :=
  if _hs : s<N then
    let next := preparedReverse I N (s+2)
    let p := next.1 + bezout.Balanced.endpointWeight (N-1-s) * preparedC I (N-1-s)
    (p, next.2 + bezout.Balanced.endpointWeight s * p / 2)
  else (0,0)
termination_by N-s

/-- The actual two-accumulator reverse preparation equals both exact parity tails. -/
theorem preparedReverse_eq (I : chebyshev1.SpectralInterval) (N s : ℕ) :
    preparedReverse I N s = (bezout.Balanced.reverseP I N s, bezout.Balanced.reverseQ I N s) := by
  rw [preparedReverse]
  split_ifs with hs
  · rw [preparedReverse_eq I N (s+2), preparedC_eq]
    have hp := bezout.Balanced.reverseP_step I hs
    have hq := bezout.Balanced.reverseQ_step I hs
    simp only [← hp]
    exact Prod.ext rfl hq.symm
  · rw [bezout.Balanced.reverseP_terminal I (by omega),
      bezout.Balanced.reverseQ_terminal I (by omega)]
termination_by N-s

/-- The printed scalar impulse recursion, independent of the synthesized history.
Use: the implementation only stores the band 1 ≤ j-k ≤ 4. -/
def preparedImpulse (I : chebyshev1.SpectralInterval) (N : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | 1, k => if k=0 then -2/I.delta else 0
  | 2, k => if k<2 then -4*I.eta*bezout.Balanced.omega N 2/I.delta else 0
  | 3, k =>
      bezout.Balanced.startup30 I N * (if k=0 then 1 else 0) +
      bezout.Balanced.startup31 I N * (if k=1 then 1 else 0) +
      (-4 * bezout.Balanced.omega N 3 * preparedNormalizer I N 2 /
        (I.delta * bezout.Balanced.omega N 2)) * (if k=2 then 1 else 0)
  | j+4, k =>
      bezout.Balanced.recurrenceA I N j * preparedImpulse I N (j+3) k +
      (1-bezout.Balanced.recurrenceC N j) * preparedImpulse I N (j+2) k -
      bezout.Balanced.recurrenceA I N j * preparedImpulse I N (j+1) k +
      bezout.Balanced.recurrenceC N j * preparedImpulse I N j k -
      bezout.Balanced.recurrenceB I N j *
        (preparedNormalizer I N (j+3) * (if k=j+3 then 1 else 0) -
         preparedNormalizer I N (j+1) * (if k=j+1 then 1 else 0))
termination_by j _ => j

/-- The scalar preparation table equals every actual causal impulse coefficient. -/
theorem preparedImpulse_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (j k : Fin N) : preparedImpulse I N j.val k.val = bezout.Balanced.impulse I N hN j k := by
  obtain ⟨j,hj⟩ := j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    match j with
    | 0 =>
      rw [preparedImpulse, bezout.Balanced.impulse_triangular I N hN _ k (by exact Nat.zero_le _)]
    | 1 => simpa only [preparedImpulse] using (bezout.Balanced.impulse_one I N hN k).symm
    | 2 => simpa only [preparedImpulse] using (bezout.Balanced.impulse_two I hN hj k).symm
    | 3 => simpa only [preparedImpulse, preparedNormalizer_eq, bezout.Balanced.startup32] using
        (bezout.Balanced.impulse_three I hN hj k).symm
    | j+4 =>
      rw [preparedImpulse, preparedNormalizer_eq, preparedNormalizer_eq,
        bezout.Balanced.impulse_recurrence I hN hj k]
      rw [ih (j+3) (by omega) (by omega), ih (j+2) (by omega) (by omega),
        ih (j+1) (by omega) (by omega), ih j (by omega) (by omega)]

/-- The printed table vanishes on and above the causal diagonal. -/
theorem preparedImpulse_triangular (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (j k : Fin N) (hjk : j ≤ k) : preparedImpulse I N j.val k.val = 0 := by
  rw [preparedImpulse_eq I N hN, bezout.Balanced.impulse_triangular I N hN j k hjk]

/-- The readout scalars computed by the two reverse parity accumulators. -/
def preparedReadout (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ :=
  4 * I.epsilon N * preparedNormalizer I N s / I.delta *
    ((preparedReverse I N s).2 / bezout.Balanced.omega N s -
      if s+2<N then (preparedReverse I N (s+2)).2 / bezout.Balanced.omega N (s+2) else 0)

/-- The reverse scalar preparation gives the exact physical output coefficient. -/
theorem preparedReadout_eq (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : preparedReadout I N s.val = (bezout.Balanced.history I N hN).b s := by
  rw [preparedReadout, preparedNormalizer_eq, preparedReverse_eq]
  by_cases hs : s.val+2<N
  · rw [ite_eq_left hs, preparedReverse_eq]
    exact (bezout.Balanced.history_readout I N hN s).symm
  · rw [ite_eq_right hs]
    have hr := bezout.Balanced.history_readout I N hN s
    rw [bezout.Balanced.reverseQ_terminal I (s := s.val+2) (by omega), zero_div, sub_zero] at hr
    simpa only [sub_zero] using hr.symm

/-- Only four impulse entries per row need storage.
Use: every previous impulse read by an entry in the stored band is either zero
by causality or belongs to the stored band of one of the four preceding rows. -/
theorem impulse_band_closed {j k d : ℕ} (hband : k<j ∧ j≤k+4)
    (hd : d≤4) (hcausal : k<j-d) : k<j-d ∧ j-d≤k+4 := by omega

end
end bezout.Algorithms.Balanced
