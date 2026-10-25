import chebyshev1.Realization.Gain
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Order.Compact

/-!
Article: chebyshev1, Proposition 1.3.
Compactness supplies a maximizing spectral pair for every finite realization.
Use: `chebyshev1.Realization.gain_attained` feeds `chebyshev1.JacobiData.gain_eq_blocks`
(The supremum formula of Theorem 4.2, with exactly the article's z-coordinate domain).
Proof chain: `chebyshev1.JacobiData.gain_eq_blocks` — chebyshev1, Theorem 4.2; Block
determinants, first-variation kernel and gain.
-/
namespace chebyshev1.Realization
noncomputable section
open scoped BigOperators Matrix.Norms.Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
Continuity of the displayed function: `Continuous (fun p => chebyshev1.orderedProduct (fun
s => C s p) n)`.

Use: `chebyshev1.Realization.continuous_kernel` uses this continuity result to establish
continuity of the displayed function: `Continuous (fun p : ℝ × ℝ => R.kernel N s p.1 p.2)`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.gain_eq_endpoint`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
private theorem continuous_product (C : ℕ → ℝ × ℝ → Matrix ι ι ℝ)
    (h : ∀ s, Continuous (C s)) (n : ℕ) :
    Continuous (fun p => chebyshev1.orderedProduct (fun s => C s p) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact (h n).mul ih

/--
Continuity of the displayed function: `Continuous (fun p : ℝ × ℝ => R.kernel N s p.1 p.2)`.

Use: `chebyshev1.Realization.continuous_kernelNorm` uses this continuity result to
establish continuity of the displayed function: `Continuous (fun p : ℝ × ℝ => R.kernelNorm N
p.1 p.2)`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.gain_eq_endpoint`.

Proof: Use the identities/estimates
`_private.chebyshev1.Realization.GainBounds.0.chebyshev1.Realization.continuous_product`
with the arguments shown in the proof.
-/
theorem continuous_kernel (R : Realization ι) (N s : ℕ) :
    Continuous (fun p : ℝ × ℝ => R.kernel N s p.1 p.2) := by
  -- Establish continuity hstep before using the function at limits or in calculus arguments.
  have hstep (t : ℕ) (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
      Continuous (fun p => R.scalarStep t (f p)) := by
    exact continuous_const.sub (hf.smul continuous_const)
  have ht := continuous_product (fun t p => R.scalarStep (s + 1 + t) p.1)
    (fun t => hstep _ _ continuous_fst) (N - (s + 1))
  have hp := continuous_product (fun t p => R.scalarStep t p.2)
    (fun t => hstep _ _ continuous_snd) s
  have hm := (ht.mul (continuous_const (y := R.queryFactor s))).mul hp
  dsimp [kernel, scalarContract]
  apply Continuous.neg
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp hm))).mul
    continuous_const

/--
Continuity of the displayed function: `Continuous (fun p : ℝ × ℝ => R.kernelNorm N p.1 p.2)`.

Use: `chebyshev1.Realization.gainValues_compact` uses this continuity result to establish
the precise assertion is `IsCompact (R.gainValues I N)`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.gain_eq_endpoint`.

Proof: Use the identities/estimates `chebyshev1.Realization.continuous_kernel` with the
arguments shown in the proof.
-/
theorem continuous_kernelNorm (R : Realization ι) (N : ℕ) :
    Continuous (fun p : ℝ × ℝ => R.kernelNorm N p.1 p.2) := by
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro s _
  exact (continuous_kernel R N s).pow 2

/--
Exact identity `R.gainValues I N = (fun p : ℝ × ℝ => R.kernelNorm N p.1 p.2) '' (Set.Icc I.mu
I.L ×ˢ Set.Icc I.mu I.L)`.

Use: `chebyshev1.Realization.gainValues_compact` rewrites with this identity to establish
the precise assertion is `IsCompact (R.gainValues I N)`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.gain_eq_endpoint`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem gainValues_eq_image (R : Realization ι) (I : SpectralInterval) (N : ℕ) :
    R.gainValues I N = (fun p : ℝ × ℝ => R.kernelNorm N p.1 p.2) ''
      (Set.Icc I.mu I.L ×ˢ Set.Icc I.mu I.L) := by
  -- The tactic block explicitly constructs the required witness or reduces the goal to the
  -- local facts stated below.
  ext v
  constructor
  · rintro ⟨lam, hl, nu, hn, rfl⟩
    exact ⟨(lam, nu), ⟨hl, hn⟩, rfl⟩
  · rintro ⟨⟨lam, nu⟩, ⟨hl, hn⟩, rfl⟩
    exact ⟨lam, hl, nu, hn, rfl⟩

/--
The precise assertion is `IsCompact (R.gainValues I N)`.

Use: `chebyshev1.Realization.gain_attained` uses this assertion to establish constructs
witnesses with the exact properties `∃ lam ∈ Set.Icc I.mu I.L, ∃ nu ∈ Set.Icc I.mu I.L,
R.kernelNorm N lam nu = R.gain I N`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.gain_eq_endpoint`.

Proof: Use the identities/estimates `chebyshev1.Realization.gainValues_eq_image`,
`chebyshev1.Realization.continuous_kernelNorm` with the arguments shown in the proof.
-/
theorem gainValues_compact (R : Realization ι) (I : SpectralInterval) (N : ℕ) :
    IsCompact (R.gainValues I N) := by
  rw [gainValues_eq_image]
  exact (isCompact_Icc.prod isCompact_Icc).image (R.continuous_kernelNorm N)

/--
The precise assertion is `(R.gainValues I N).Nonempty`.

Use: `chebyshev1.Realization.gain_attained` uses this assertion to establish constructs
witnesses with the exact properties `∃ lam ∈ Set.Icc I.mu I.L, ∃ nu ∈ Set.Icc I.mu I.L,
R.kernelNorm N lam nu = R.gain I N`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.gain_eq_endpoint`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem gainValues_nonempty (R : Realization ι) (I : SpectralInterval) (N : ℕ) :
    (R.gainValues I N).Nonempty :=
  ⟨_, I.mu, ⟨le_rfl, I.mu_lt_L.le⟩, I.mu, ⟨le_rfl, I.mu_lt_L.le⟩, rfl⟩

/--
The stated quantitative bound `R.kernelNorm N lam nu ≤ R.gain I N`.

Use: `chebyshev1.Realization.gain_nonneg` uses this bound to establish the stated
quantitative bound `0 ≤ R.gain I N`.

Article: chebyshev1, Theorem E.1 via `chebyshev1.SineJacobi.gain_eq_endpoint`.

Proof: Use the identities/estimates `chebyshev1.Realization.gainValues_compact` with the
arguments shown in the proof.
-/
theorem kernelNorm_le_gain (R : Realization ι) (I : SpectralInterval) (N : ℕ)
    {lam nu : ℝ} (hl : lam ∈ Set.Icc I.mu I.L) (hn : nu ∈ Set.Icc I.mu I.L) :
    R.kernelNorm N lam nu ≤ R.gain I N :=
  le_csSup (R.gainValues_compact I N).bddAbove ⟨lam, hl, nu, hn, rfl⟩

/--
The stated quantitative bound `0 ≤ R.gain I N`.

Use: `chebyshev1.Realization.diagonal_entry_bound` uses this bound to establish the stated
quantitative bound `(R.linearResponse N (Matrix.diagonal eig) E i j) ^ 2 ≤ (R.gain I N) ^ 2 * ∑
s ∈ Finset.range N, (E s i j) ^ 2`.

Article: chebyshev1, Proposition 1.3 via `chebyshev1.Realization.hs_constant_minimal`.

Proof: Use the identities/estimates `chebyshev1.Realization.kernelNorm_le_gain` with the
arguments shown in the proof.
-/
theorem gain_nonneg (R : Realization ι) (I : SpectralInterval) (N : ℕ) :
    0 ≤ R.gain I N :=
  (Real.sqrt_nonneg _).trans (R.kernelNorm_le_gain I N
    ⟨le_rfl, I.mu_lt_L.le⟩ ⟨le_rfl, I.mu_lt_L.le⟩)

/--
Compactness supplies a maximizing spectral pair for every finite realization.

Constructs witnesses with the exact properties `∃ lam ∈ Set.Icc I.mu I.L, ∃ nu ∈ Set.Icc I.mu
I.L, R.kernelNorm N lam nu = R.gain I N`.

Use: `chebyshev1.JacobiData.gain_eq_blocks` uses this identity to establish the identity
`(J.realization I).gain I N = (2 / (I.delta * |J.den I N|)) * sSup (J.blockGainValues N)`.

Article: chebyshev1, Proposition 1.3.

Proof: Use the identities/estimates `chebyshev1.Realization.gainValues_compact`,
`chebyshev1.Realization.gainValues_nonempty` with the arguments shown in the proof.
-/
theorem gain_attained (R : Realization ι) (I : SpectralInterval) (N : ℕ) :
    ∃ lam ∈ Set.Icc I.mu I.L, ∃ nu ∈ Set.Icc I.mu I.L,
      R.kernelNorm N lam nu = R.gain I N := by
  have hm := (R.gainValues_compact I N).sSup_mem (R.gainValues_nonempty I N)
  obtain ⟨lam, hl, nu, hn, he⟩ := hm
  exact ⟨lam, hl, nu, hn, he.symm⟩

end
end chebyshev1.Realization
