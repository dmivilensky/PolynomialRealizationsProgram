import bezout.Channel.Roots.Algebra
import bezout.Comparisons.Competitors.Stepsize

/-!
Article: bezout, Proposition D.1, actual Chebyshev root-step histories.
Use: connects every root ordering, including literal LF/fractal, to a genuine
N-call causal oracle history and its physical insertion coefficients.
Proof: the exact zero-momentum propagation theorem, finite product identity,
and unconditional omitted-factor polynomial formula.
-/

namespace bezout.Channel.Roots
noncomputable section
open Polynomial
open scoped BigOperators

/-- The actual causal history of a prescribed finite gradient-step schedule. -/
def history {N : ℕ} (α : Fin N → ℝ) : bezout.History N :=
  Comparisons.Competitors.Stepsize.history N (extend α)

/-- Its actual terminal is the full affine product of the prescribed steps. -/
theorem history_terminal {N : ℕ} (α : Fin N → ℝ) : (history α).terminal=terminal α := by
  rw [history,Comparisons.Competitors.Stepsize.terminal,polynomial_extend]

/-- Every permutation of the explicitly constructed Chebyshev roots is terminal-exact. -/
theorem history_exact (I : chebyshev1.SpectralInterval) (N : ℕ) (e : Equiv.Perm (Fin N)) :
    (history (steps I N e)).ChebyshevExact I := by
  rw [bezout.History.ChebyshevExact,history_terminal,terminal_steps_eq]

/-- The literal recursively interlaced LF schedule as an actual oracle history. -/
def lfHistory (I : chebyshev1.SpectralInterval) (k : ℕ) : bezout.History (2^k) :=
  history (steps I (2^k) (dyadicPermutation k))

/-- The actual LF/fractal method has the exact desired Chebyshev terminal. -/
theorem lfHistory_exact (I : chebyshev1.SpectralInterval) (k : ℕ) :
    (lfHistory I k).ChebyshevExact I := history_exact I (2^k) (dyadicPermutation k)

/-- The diagonal physical kernel of the actual history is its omitted-factor polynomial. -/
theorem history_diagonalKernel {N : ℕ} (α : Fin N → ℝ) (s : Fin N) (x : ℝ) :
    Lower.physicalKernel (history α) s x x=diagonalProfile α s x := by
  unfold Lower.physicalKernel
  rw [← bezout.History.realization_kernel,history,
    Comparisons.Competitors.Stepsize.realization_kernel]
  exact diagonalKernel_extend α s x

/-- The quotient formula is a consequence of the actual causal history, off its own root. -/
theorem history_root_quotient (I : chebyshev1.SpectralInterval) (N : ℕ)
    (e : Equiv.Perm (Fin N)) (s : Fin N) (x : ℝ) (hx : node I N (e s)≠x) :
    Lower.physicalKernel (history (steps I N e)) s x x=
      -(I.residual N).eval x/(node I N (e s)-x) := by
  rw [history_diagonalKernel]
  have ha := ne_of_gt (steps_pos I N e s)
  have hinv : (steps I N e s)⁻¹=node I N (e s) := by simp [steps]
  rw [diagonalProfile_quotient _ _ _ ha (by simpa only [hinv] using hx),terminal_steps_eq,hinv]

/-- Every ordering changes the actual diagonal kernel solely by a temporal reindexing. -/
theorem history_diagonal_permute {N : ℕ} (α : Fin N → ℝ) (e : Equiv.Perm (Fin N))
    (s : Fin N) (x : ℝ) :
    Lower.physicalKernel (history (α ∘ e)) s x x = Lower.physicalKernel (history α) (e s) x x := by
  rw [history_diagonalKernel,history_diagonalKernel,diagonalProfile_permute]

/-- Finite chronological indexing recovers the exact derivative correlation identity. -/
theorem profile_crossEnergy {N : ℕ} (α : Fin N → ℝ) (x y : ℝ) :
    (∑ s : Fin N, diagonalProfile α s x*diagonalProfile α s y)=crossEnergy (extend α) N x y := by
  simp_rw [← diagonalKernel_extend α]
  rw [Fin.sum_univ_eq_sum_range
    (fun s : ℕ => diagonalKernel (extend α) N s x*diagonalKernel (extend α) N s y) N]
  rfl

/-- The actual diagonal physical profile has the same exact full correlation. -/
theorem history_crossEnergy {N : ℕ} (α : Fin N → ℝ) (x y : ℝ) :
    (∑ s : Fin N, Lower.physicalKernel (history α) s x x*
      Lower.physicalKernel (history α) s y y)=crossEnergy (extend α) N x y := by
  simp only [history_diagonalKernel]
  exact profile_crossEnergy α x y

/-- The full actual endpoint energy is independent of the root ordering. -/
theorem history_endpointEnergy_mu (I : chebyshev1.SpectralInterval) (N : ℕ)
    (e : Equiv.Perm (Fin N)) :
    Lower.physicalKernelSq (history (steps I N e)) I.mu I.mu =
      (2*I.epsilon N/I.delta)^2*((2*(N:ℝ)^4+(N:ℝ)^2)/3) := by
  unfold Lower.physicalKernelSq
  simp only [pow_two]
  rw [history_crossEnergy]
  simpa only [schedule_eq_extend,pow_two] using endpointEnergy_mu _ I N (schedule_finalExact I N e)

/-- The actual even-horizon upper endpoint has the same exact squared norm. -/
theorem history_endpointEnergy_L (I : chebyshev1.SpectralInterval) (N : ℕ)
    (hN : Even N) (e : Equiv.Perm (Fin N)) :
    Lower.physicalKernelSq (history (steps I N e)) I.L I.L =
      (2*I.epsilon N/I.delta)^2*((2*(N:ℝ)^4+(N:ℝ)^2)/3) := by
  unfold Lower.physicalKernelSq
  simp only [pow_two]
  rw [history_crossEnergy]
  simpa only [schedule_eq_extend,pow_two] using endpointEnergy_L _ I N hN (schedule_finalExact I N e)

/-- The two actual endpoint time profiles have the stated exact negative correlation. -/
theorem history_endpointCross (I : chebyshev1.SpectralInterval) (N : ℕ)
    (hN : Even N) (e : Equiv.Perm (Fin N)) :
    (∑ s : Fin N, Lower.physicalKernel (history (steps I N e)) s I.mu I.mu*
      Lower.physicalKernel (history (steps I N e)) s I.L I.L) =
      -(2*I.epsilon N/I.delta)^2*(N:ℝ)^2 := by
  rw [history_crossEnergy]
  exact endpointCross_even _ I N hN (schedule_finalExact I N e)

end
end bezout.Channel.Roots
