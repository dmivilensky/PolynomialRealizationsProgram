import krylov.Envelope.RawSchurJacobi
import krylov.LinearAlgebra.JacobiStrictPrefix
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), actual infinite-sequence finite Jacobi prefixes.
Use: represent the genuine finite Gauss matrices of the original Jacobi coefficient sequence and derive actual positive original and shifted principal domains.
Source: the original true three-diagonal entries, actual finite principal compression and the proved strict positive proper-prefix theorem.
-/

namespace krylov.Reference
noncomputable section
open krylov.Realization krylov.LinearAlgebra Matrix

/-- The actual finite negative-residual Jacobi prefix formed from the original diagonal and positive edge sequence.
Use: The actual finite negative-residual Jacobi prefix formed from the original diagonal and positive edge sequence.
Article: main_krylov, prop:phi(c), actual infinite-sequence finite Jacobi prefixes.
Proof: Use the genuine chronological diagonal and adjacent physical entries. -/
def jacobiPrefix (A B : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => if i=j then A i.val else if i.val+1=j.val then -B i.val else if j.val+1=i.val then -B j.val else 0

/-- Every actual Jacobi prefix diagonal is its original true sequence coefficient.
Use: Every actual Jacobi prefix diagonal is its original true sequence coefficient.
Article: main_krylov, prop:phi(c), actual infinite-sequence finite Jacobi prefixes.
Proof: Read the genuine physical diagonal entry. -/
theorem jacobiPrefix_diagonal (A B : ℕ → ℝ) (N : ℕ) (i : Fin N) :
    jacobiPrefix A B N i i=A i.val := by
  simp [jacobiPrefix]

/-- Every actual real Jacobi prefix is genuinely Hermitian.
Use: Every actual real Jacobi prefix is genuinely Hermitian.
Article: main_krylov, prop:phi(c), actual infinite-sequence finite Jacobi prefixes.
Proof: Its original diagonal is real and the true adjacent physical entries match across the diagonal. -/
theorem jacobiPrefix_isHermitian (A B : ℕ → ℝ) (N : ℕ) : (jacobiPrefix A B N).IsHermitian := by
  -- The actual lower and upper edges share exactly their original chronological coupling.
  apply Matrix.isHermitian_iff_isSymm.mpr
  ext i j
  by_cases hij : i=j
  · subst j
    rfl
  · by_cases h1 : i.val+1=j.val
    · simp [jacobiPrefix,hij,Ne.symm hij,h1,show ¬ j.val+1=i.val by omega]
    · by_cases h2 : j.val+1=i.val
      · simp [jacobiPrefix,hij,Ne.symm hij,h1,h2]
      · simp [jacobiPrefix,hij,Ne.symm hij,h1,h2]

/-- Every genuine leading principal block is the actual shorter original Jacobi prefix.
Use: Every genuine leading principal block is the actual shorter original Jacobi prefix.
Article: main_krylov, prop:phi(c), actual infinite-sequence finite Jacobi prefixes.
Proof: Read the same original chronological physical indices. -/
theorem jacobiPrefix_leading (A B : ℕ → ℝ) (N m : ℕ) (hm : m≤N) :
    rawBlock (jacobiPrefix A B N) 0 m (by omega)=jacobiPrefix A B m := by
  ext i j
  simp [rawBlock,jacobiPrefix,Fin.ext_iff]

/-- Every actual Jacobi prefix has the genuine three-diagonal band.
Use: Every actual Jacobi prefix has the genuine three-diagonal band.
Article: main_krylov, prop:phi(c), actual infinite-sequence finite Jacobi prefixes.
Proof: Its original entries vanish outside the true adjacent sites. -/
theorem jacobiPrefix_tridiagonal (A B : ℕ → ℝ) (N : ℕ) :
    ∀ i j : Fin N,i.val+1 < j.val ∨ j.val+1 < i.val → jacobiPrefix A B N i j=0 := by
  intro i j hij
  simp [jacobiPrefix,show i≠j by intro h;subst j;omega,
    show ¬ i.val+1=j.val by omega,show ¬ j.val+1=i.val by omega]

/-- Every genuine adjacent entry is strictly negative when the actual original edges are positive.
Use: Every genuine adjacent entry is strictly negative when the actual original edges are positive.
Article: main_krylov, prop:phi(c), actual infinite-sequence finite Jacobi prefixes.
Proof: Read the true original physical coupling. -/
theorem jacobiPrefix_adjacent_neg (A B : ℕ → ℝ) (hB : ∀ n,0 < B n) (N : ℕ) :
    ∀ i j : Fin N,i.val+1=j.val → jacobiPrefix A B N i j < 0 := by
  intro i j hij
  rw [jacobiPrefix,ite_eq_right (show i≠j by intro h;subst j;omega),ite_eq_left hij]
  exact neg_neg_of_pos (hB i.val)

/-- Shifting the actual sequence diagonal subtracts the genuine scalar identity from every original finite prefix.
Use: Shifting the actual sequence diagonal subtracts the genuine scalar identity from every original finite prefix.
Article: main_krylov, prop:phi(c), actual infinite-sequence finite Jacobi prefixes.
Proof: Compare actual diagonal and off-diagonal physical entries. -/
theorem jacobiPrefix_shift (A B : ℕ → ℝ) (mu : ℝ) (N : ℕ) :
    jacobiPrefix (fun n => A n-mu) B N=jacobiPrefix A B N-mu • 1 := by
  ext i j
  by_cases hij : i=j <;> simp [jacobiPrefix,hij]

/-- A genuine positive physical lower spectral shift makes the actual original Jacobi prefix positive definite.
Use: A genuine positive physical lower spectral shift makes the actual original Jacobi prefix positive definite.
Article: main_krylov, prop:phi(c), actual infinite-sequence finite Jacobi prefixes.
Proof: Add the true positive scalar identity form to the actual semidefinite shifted form. -/
theorem jacobiPrefix_posDef (A B : ℕ → ℝ) (mu : ℝ) (hmu : 0 < mu) (N : ℕ)
    (hlo : (jacobiPrefix A B N-mu • 1).PosSemidef) : (jacobiPrefix A B N).PosDef := by
  have hp : (mu • (1 : Matrix (Fin N) (Fin N) ℝ)).PosDef := by
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.PosDef.diagonal (fun _ => hmu)
  have h := hp.add_posSemidef hlo
  have he : mu • (1 : Matrix (Fin N) (Fin N) ℝ)+(jacobiPrefix A B N-mu • 1)=jacobiPrefix A B N := by module
  rwa [he] at h

/-- Every actual lower-shifted prefix is genuinely positive definite when all original finite shifted forms are semidefinite and true edges are nonzero.
Use: Every actual lower-shifted prefix is genuinely positive definite when all original finite shifted forms are semidefinite and true edges are nonzero.
Article: main_krylov, prop:phi(c), actual infinite-sequence finite Jacobi prefixes.
Proof: One real additional original Jacobi site supplies the genuine strict positive proper-prefix margin. -/
theorem jacobiPrefix_shift_posDef (A B : ℕ → ℝ) (mu : ℝ)
    (hB : ∀ n,0 < B n) (hlo : ∀ N,(jacobiPrefix A B N-mu • 1).PosSemidef) (N : ℕ) :
    (jacobiPrefix (fun n => A n-mu) B N).PosDef := by
  -- A real additional prefix site turns the original weak lower spectral window into a genuine strict shifted inverse domain.
  let C := fun n => A n-mu
  have hp : (jacobiPrefix C B (N+1)).PosSemidef := by rw [jacobiPrefix_shift];exact hlo (N+1)
  have hsym := jacobiPrefix_isHermitian C B (N+1)
  have hneg := jacobiPrefix_adjacent_neg C B hB (N+1)
  have hh := jacobi_strict_prefix _ hp (jacobiPrefix_tridiagonal C B (N+1)) (by
    intro i j hij
    have he : jacobiPrefix C B (N+1) j i=jacobiPrefix C B (N+1) i j :=
      congrFun (congrFun hsym i) j
    rw [he]
    exact (hneg i j hij).ne)
  have he : (jacobiPrefix C B (N+1)).submatrix Fin.castSucc Fin.castSucc=jacobiPrefix C B N := by
    ext i j
    simp [jacobiPrefix,Fin.ext_iff]
  rw [he] at hh
  exact hh
end
end krylov.Reference
