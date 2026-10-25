import chebyshev1.TwoTerm.Uniqueness
import chebyshev1.Prefix.Asymptotics

/-!
Article: chebyshev1, Theorem 3.1.
The asymptotic optimal value for any family of finite prefix-exact recurrences.
Result: `chebyshev1.TwoTerm.optimal_asymptotic` supplies the stated article conclusion.
-/
namespace chebyshev1.TwoTerm
noncomputable section
open scoped Matrix BigOperators Topology Asymptotics

/--
Exact identity `S.gamma s = Prefix.gamma I s`.

Use: `chebyshev1.TwoTerm.kernel_eq_prefix` rewrites with this identity to establish exact
identity `S.realization.kernel N s lam nu = (Prefix.realization I).kernel N s lam nu`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.initial_unique`,
`chebyshev1.TwoTerm.coefficients_unique` with the arguments shown in the proof.
-/
theorem gamma_eq_prefix (S : TwoTerm) (I : SpectralInterval) (N s : ℕ)
    (hs : s < N) (h : S.PrefixExact I N) : S.gamma s = Prefix.gamma I s := by
  cases s with
  | zero => exact initial_unique S I N (by omega) h
  | succ s => exact (coefficients_unique S I N (s + 1) (by omega) hs h).2.2

/--
Exact identity `S.realization.scalarStep s lam = (Prefix.realization I).scalarStep s lam`.

Use: `chebyshev1.TwoTerm.kernel_eq_prefix` uses this identity to establish the identity
`S.realization.kernel N s lam nu = (Prefix.realization I).kernel N s lam nu`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.kernel_eq_prefix`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem scalarStep_eq_prefix (S : TwoTerm) (I : SpectralInterval) (N s : ℕ)
    (hs : s < N) (h : S.PrefixExact I N) (lam : ℝ) :
    S.realization.scalarStep s lam = (Prefix.realization I).scalarStep s lam := by
  -- Check each member of the finite index type; no case is omitted.
  cases s with
  | zero =>
    have hg := gamma_eq_prefix S I N 0 hs h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Realization.scalarStep, Realization.queryFactor, Matrix.vecMulVec,
        realization, Prefix.realization, hg]
  | succ s =>
    obtain ⟨ha, hb, hg⟩ := coefficients_unique S I N (s + 1) (by omega) hs h
    rw [scalarStep_succ, Prefix.algorithmStep_succ, ha, hb, hg, Prefix.gamma_succ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring

/--
Exact identity `S.realization.kernel N s lam nu = (Prefix.realization I).kernel N s lam nu`.

Use: `chebyshev1.TwoTerm.kernelNorm_eq_prefix` rewrites with this identity to establish
exact identity `S.realization.kernelNorm N lam nu = (Prefix.realization I).kernelNorm N lam
nu`.

Article: chebyshev1, Theorem 3.1.

Proof: Use the identities/estimates `chebyshev1.orderedProduct_congr`,
`chebyshev1.TwoTerm.scalarStep_eq_prefix`, `chebyshev1.TwoTerm.queryFactor` with the
arguments shown in the proof.
-/
theorem kernel_eq_prefix (S : TwoTerm) (I : SpectralInterval) (N s : ℕ)
    (hs : s < N) (h : S.PrefixExact I N) (lam nu : ℝ) :
    S.realization.kernel N s lam nu = (Prefix.realization I).kernel N s lam nu := by
  -- Use the identities/estimates `chebyshev1.orderedProduct_congr`,
  -- `chebyshev1.TwoTerm.scalarStep_eq_prefix`, `chebyshev1.TwoTerm.queryFactor` with
  -- the arguments shown in the proof.
  have hp : orderedProduct (fun i => S.realization.scalarStep i nu) s =
      orderedProduct (fun i => (Prefix.realization I).scalarStep i nu) s :=
    orderedProduct_congr (fun i hi => scalarStep_eq_prefix S I N i (by omega) h nu)
  have ht : orderedProduct (fun i => S.realization.scalarStep (s + 1 + i) lam) (N - (s + 1)) =
      orderedProduct (fun i => (Prefix.realization I).scalarStep (s + 1 + i) lam) (N - (s + 1)) :=
    orderedProduct_congr (fun i hi => scalarStep_eq_prefix S I N (s + 1 + i) (by omega) h lam)
  have hq : S.realization.queryFactor s = (Prefix.realization I).queryFactor s := by
    rw [queryFactor, Prefix.queryFactor, gamma_eq_prefix S I N s hs h]
  rw [Realization.kernel, Realization.kernel, scalarContract, Prefix.scalarContract, hp, ht, hq]

/--
Exact identity `S.realization.kernelNorm N lam nu = (Prefix.realization I).kernelNorm N lam
nu`.

Use: `chebyshev1.TwoTerm.gain_eq_prefix` rewrites with this identity to establish exact
identity `S.realization.gain I N = (Prefix.realization I).gain I N`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.gain_eq_prefix`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem kernelNorm_eq_prefix (S : TwoTerm) (I : SpectralInterval) (N : ℕ)
    (h : S.PrefixExact I N) (lam nu : ℝ) :
    S.realization.kernelNorm N lam nu = (Prefix.realization I).kernelNorm N lam nu := by
  unfold Realization.kernelNorm
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro s hs
  rw [kernel_eq_prefix S I N s (Finset.mem_range.mp hs) h]

/--
Prefix exactness forces equality of the entire gain, stronger than the lower bound.

Exact identity `S.realization.gain I N = (Prefix.realization I).gain I N`.

Use: `chebyshev1.TwoTerm.optimal_asymptotic` uses this identity to establish the stated
quantitative bound `(fun N : ℕ => (S N).realization.gain I N) ~[Filter.atTop] (fun N : ℕ => (4
/ Real.sqrt 3) * (N : ℝ) ^ (3 / 2 : ℝ) * I.epsilon N / I.delta)`.

Article: chebyshev1, Theorem 3.1.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.kernelNorm_eq_prefix` with the
arguments shown in the proof.
-/
theorem gain_eq_prefix (S : TwoTerm) (I : SpectralInterval) (N : ℕ)
    (h : S.PrefixExact I N) : S.realization.gain I N = (Prefix.realization I).gain I N := by
  unfold Realization.gain Realization.gainValues
  simp_rw [kernelNorm_eq_prefix S I N h]

/--
Theorem 3.1: every recurrence in the class has the same exact optimal value.

Exact identity `S.realization.gain I N = I.epsilon N / I.delta * Real.sqrt (4 * (N : ℝ) ^ 2 +
16 * ∑ m ∈ Finset.range N, (m : ℝ) ^ 2)`.

Use: `chebyshev1.TwoTerm.optimal_lower_bound` uses this identity to establish the stated
quantitative bound `I.epsilon N / I.delta * Real.sqrt (4 * (N : ℝ) ^ 2 + 16 * ∑ m ∈
Finset.range N, (m : ℝ) ^ 2) ≤ S.realization.gain I N`.

Article: chebyshev1, Theorem 3.1.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.gain_eq_prefix`,
`chebyshev1.Prefix.gain_exact_sum` with the arguments shown in the proof.
-/
theorem optimal_gain (S : TwoTerm) (I : SpectralInterval) (N : ℕ) (hN : 1 ≤ N)
    (h : S.PrefixExact I N) : S.realization.gain I N = I.epsilon N / I.delta *
      Real.sqrt (4 * (N : ℝ) ^ 2 + 16 * ∑ m ∈ Finset.range N, (m : ℝ) ^ 2) := by rw [gain_eq_prefix S I N h, Prefix.gain_exact_sum I N hN]

/--
The stated quantitative bound `I.epsilon N / I.delta * Real.sqrt (4 * (N : ℝ) ^ 2 + 16 * ∑ m ∈
Finset.range N, (m : ℝ) ^ 2) ≤ S.realization.gain I N`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev1, Theorem 3.1.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.optimal_gain` with the arguments
shown in the proof.
-/
theorem optimal_lower_bound (S : TwoTerm) (I : SpectralInterval) (N : ℕ) (hN : 1 ≤ N)
    (h : S.PrefixExact I N) : I.epsilon N / I.delta *
      Real.sqrt (4 * (N : ℝ) ^ 2 + 16 * ∑ m ∈ Finset.range N, (m : ℝ) ^ 2) ≤
        S.realization.gain I N := (optimal_gain S I N hN h).ge

/--
Constructs `standard` of type `TwoTerm` by the displayed record fields. Data fields specify the
construction; proof fields discharge its required properties.

Use: `chebyshev1.TwoTerm.standard_prefixExact` uses this definition to establish the
precise assertion is `(standard I).PrefixExact I N`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.standard_attains`.
-/
def standard (I : SpectralInterval) : TwoTerm where
  a := fun t => 1 + Prefix.beta I t
  b := fun t => -Prefix.beta I t
  gamma := Prefix.gamma I

/--
Exact identity `(standard I).realization.scalarStep s lam = (Prefix.realization I).scalarStep s
lam`.

Use: `chebyshev1.TwoTerm.standard_prefixExact` uses this identity to establish the precise
assertion is `(standard I).PrefixExact I N`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.standard_attains`.

Proof: Check each member of the finite index type; no case is omitted.
-/
theorem standard_step (I : SpectralInterval) (s : ℕ) (lam : ℝ) :
    (standard I).realization.scalarStep s lam = (Prefix.realization I).scalarStep s lam := by
  -- Check each member of the finite index type; no case is omitted.
  cases s with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Realization.scalarStep, Realization.queryFactor, Matrix.vecMulVec,
        realization, Prefix.realization, standard]
  | succ s =>
    rw [scalarStep_succ, Prefix.algorithmStep_succ]
    dsimp [standard]
    rw [Prefix.gamma_succ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring

/--
The precise assertion is `(standard I).PrefixExact I N`.

Use: `chebyshev1.TwoTerm.standard_attains` uses this assertion to establish the identity
`(standard I).PrefixExact I N ∧ (standard I).realization.gain I N = I.epsilon N / I.delta *
Real.sqrt (4 * (N : ℝ) ^ 2 + 16 * ∑ m ∈ Finset.range N, (m : ℝ) ^ 2)`.

Article: chebyshev1, Theorem 3.1 via `chebyshev1.TwoTerm.standard_attains`.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.scalarContract`,
`chebyshev1.orderedProduct_congr`, `chebyshev1.TwoTerm.standard_step` with the
arguments shown in the proof.
-/
theorem standard_prefixExact (I : SpectralInterval) (N : ℕ) : (standard I).PrefixExact I N := by
  intro t _ lam _
  rw [Realization.scalarTransfer, scalarContract]
  have hp : orderedProduct (fun s => (standard I).realization.scalarStep s lam) t =
      orderedProduct (fun s => (Prefix.realization I).scalarStep s lam) t :=
    orderedProduct_congr (fun s _ => standard_step I s lam)
  rw [hp]
  simpa only [Realization.scalarTransfer, Prefix.scalarContract] using Prefix.scalar_exact I t lam

/--
The standard recurrence belongs to the class and attains the bound of 3.1.

Exact identity `(standard I).PrefixExact I N ∧ (standard I).realization.gain I N = I.epsilon N
/ I.delta * Real.sqrt (4 * (N : ℝ) ^ 2 + 16 * ∑ m ∈ Finset.range N, (m : ℝ) ^ 2)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem 3.1.

Proof: Use the identities/estimates `chebyshev1.TwoTerm.standard_prefixExact`,
`chebyshev1.TwoTerm.optimal_gain` with the arguments shown in the proof.
-/
theorem standard_attains (I : SpectralInterval) (N : ℕ) (hN : 1 ≤ N) :
    (standard I).PrefixExact I N ∧ (standard I).realization.gain I N = I.epsilon N / I.delta *
      Real.sqrt (4 * (N : ℝ) ^ 2 + 16 * ∑ m ∈ Finset.range N, (m : ℝ) ^ 2) :=
  ⟨standard_prefixExact I N, optimal_gain _ I N hN (standard_prefixExact I N)⟩

/--
The asymptotic optimal value for any family of finite prefix-exact recurrences.

The stated quantitative bound `(fun N : ℕ => (S N).realization.gain I N) ~[Filter.atTop] (fun N
: ℕ => (4 / Real.sqrt 3) * (N : ℝ) ^ (3 / 2 : ℝ) * I.epsilon N / I.delta)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem 3.1.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem optimal_asymptotic (I : SpectralInterval) (S : ℕ → TwoTerm)
    (h : ∀ N, (S N).PrefixExact I N) :
    (fun N : ℕ => (S N).realization.gain I N) ~[Filter.atTop]
      (fun N : ℕ => (4 / Real.sqrt 3) * (N : ℝ) ^ (3 / 2 : ℝ) * I.epsilon N / I.delta) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have heq : (fun N : ℕ => (S N).realization.gain I N) =
      (fun N : ℕ => (Prefix.realization I).gain I N) :=
    funext (fun N => gain_eq_prefix (S N) I N (h N))
  rw [heq]
  exact Prefix.gain_isEquivalent_rpow I

end
end chebyshev1.TwoTerm
