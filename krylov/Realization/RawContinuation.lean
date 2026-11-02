import krylov.Realization.RawTail
import chebyshev1.Jacobi.Resolvent

/-!
Article: main_krylov, prop:dict(i) and apF:twotail, actual continuation determinant.
Use: identify the sum of the genuine independent-injection responses with
the original matrix whose actual diagonal suffix is shifted.
Source: standard diagonal cofactor multilinearity and tridiagonal separation;
reuse the existing exact finite splitIndex bijection of PasechnyukTakac26.
-/

namespace krylov.Realization
noncomputable section
open Matrix chebyshev1
open scoped BigOperators

/-- The actual physical matrix with only its diagonal suffix shifted.
Use: the source continuation determinant retains the true unshifted leading block.
Article: main_krylov, apF:twotail. -/
def rawSuffixShift {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (j : ℕ) (lam : ℝ) :
    Matrix (Fin N) (Fin N) ℝ := T-Matrix.diagonal (fun i => if j ≤ i.val then lam else 0)


/-- A true shifted contiguous-block determinant is independent of an equal finite size's indexing presentation.
Use: transport natural tail-length arithmetic without changing any physical matrix entry.
Article: main_krylov, prop:dict(i).
Proof: substitute the equal sizes; proof irrelevance identifies the genuine bounds. -/
theorem rawBlock_shifted_det_congr {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ)
    (a m k : ℕ) (hm : a+m≤N) (hk : a+k≤N) (he : m=k) (lam : ℝ) :
    (rawBlock T a m hm-lam • 1).det=(rawBlock T a k hk-lam • 1).det := by
  subst k
  rfl

/-- Deleting a physical tridiagonal site separates its genuine leading and trailing principal blocks.
Use: compute the real diagonal cofactor, without positivity or symmetry assumptions.
Article: main_krylov, apF:twotail.
Proof: the existing finite split bijection lists the sites before and after
the deleted site. The far-band hypothesis makes the two cross blocks zero. -/
theorem raw_minor_split {n : ℕ} (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (htri : ∀ i j : Fin (n+1), i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (s : Fin (n+1)) :
    T.submatrix (fun i => s.succAbove (JacobiData.splitIndex n s i))
      (fun i => s.succAbove (JacobiData.splitIndex n s i))=
      Matrix.fromBlocks (rawBlock T 0 s.val (by omega)) 0 0
        (rawBlock T (s.val+1) (n-s.val) (by omega)) := by
  -- The real deleted-site indexing separates the two genuine sides of the physical tridiagonal band.
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change T _ _=T _ _
      congr 1 <;> apply Fin.ext <;> simp
    | inr j =>
      change T _ _=0
      apply htri
      left
      simp only [JacobiData.skip_split_left,JacobiData.skip_split_right]
      omega
  | inr i =>
    cases j with
    | inl j =>
      change T _ _=0
      apply htri
      right
      simp only [JacobiData.skip_split_left,JacobiData.skip_split_right]
      omega
    | inr j =>
      change T _ _=T _ _
      congr 1 <;> apply Fin.ext <;> simp

/-- The actual deleted-site tridiagonal determinant factors into its two genuine contiguous block determinants.
Use: the continuation increment uses exactly the unshifted leading and shifted trailing cofactors.
Article: main_krylov, apF:twotail.
Proof: reindex the actual minor by the proved split bijection and apply the standard block triangular determinant identity. -/
theorem raw_minor_det {n : ℕ} (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (htri : ∀ i j : Fin (n+1), i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (s : Fin (n+1)) :
    (T.submatrix s.succAbove s.succAbove).det=
      (rawBlock T 0 s.val (by omega)).det*(rawBlock T (s.val+1) (n-s.val) (by omega)).det := by
  have hd := Matrix.det_submatrix_equiv_self (JacobiData.splitIndex n s)
    (T.submatrix s.succAbove s.succAbove)
  rw [Matrix.submatrix_submatrix] at hd
  simp only [Function.comp_def] at hd
  rw [raw_minor_split T htri s,Matrix.det_fromBlocks_zero₂₁] at hd
  exact hd.symm

/-- Changing a single real diagonal entry changes the genuine determinant by that scalar times its actual principal cofactor.
Use: the continuation telescope follows from real determinant multilinearity.
Article: main_krylov, apF:twotail.
Proof: split the actual updated row by multilinearity; its single-coordinate
part is the genuine diagonal adjugate entry, whose cofactor sign is positive. -/
theorem det_diagonal_row {n : ℕ} (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (s : Fin (n+1)) (lam : ℝ) :
    (T.updateRow s (T s+lam • Pi.single s 1)).det=
      T.det+lam*(T.submatrix s.succAbove s.succAbove).det := by
  rw [Matrix.det_updateRow_add,Matrix.updateRow_eq_self,Matrix.det_updateRow_smul]
  have hco : (T.updateRow s (Pi.single s 1)).det=(T.submatrix s.succAbove s.succAbove).det := by
    rw [← Matrix.adjugate_apply,
      Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [show s.val+s.val=2*s.val by omega,pow_mul,neg_one_sq,one_pow,one_mul]
  rw [hco]

/-- Shifting any true diagonal suffix preserves the supplied physical tridiagonal far band.
Use: the real intermediate matrices satisfy the actual deleted-site splitting theorem.
Article: main_krylov, apF:twotail.
Proof: a far-band pair is off the diagonal, so the diagonal shift contributes zero. -/
theorem rawSuffixShift_tridiagonal {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (j : ℕ) (lam : ℝ) :
    ∀ a b : Fin N, a.val+1 < b.val ∨ b.val+1 < a.val → rawSuffixShift T j lam a b=0 := by
  intro a b hab
  have hne : a≠b := by intro he; subst b; omega
  simp only [rawSuffixShift,Matrix.sub_apply,Matrix.diagonal_apply_ne _ hne,sub_zero]
  exact htri a b hab

/-- A genuine principal block entirely before the shifted suffix is unchanged.
Use: the diagonal cofactor contains the true unshifted leading determinant.
Article: main_krylov, apF:twotail.
Proof: every diagonal index lies strictly before the cutoff; off-diagonal entries are unchanged. -/
theorem rawBlock_suffixShift_before {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ)
    (j a m : ℕ) (h : a+m≤N) (hcut : a+m≤j) (lam : ℝ) :
    rawBlock (rawSuffixShift T j lam) a m h=rawBlock T a m h := by
  -- The actual contiguous embedding determines whether each true diagonal index is shifted.
  ext i k
  change T _ _-(Matrix.diagonal (fun q : Fin N => if j ≤ q.val then lam else 0)) _ _=T _ _
  dsimp only
  by_cases hik : i=k
  · subst k
    rw [Matrix.diagonal_apply_eq,ite_eq_right (by dsimp only; have := i.isLt; omega),sub_zero]
  · rw [Matrix.diagonal_apply_ne _ (by intro he; apply hik; apply Fin.ext; have hval := congrArg Fin.val he; dsimp only at hval; omega),sub_zero]

/-- A genuine principal block entirely inside the shifted suffix receives the full scalar diagonal shift.
Use: the actual diagonal cofactor contains the printed true shifted tail.
Article: main_krylov, apF:twotail.
Proof: all actual block indices are above the cutoff, so the shift is exactly the scalar identity. -/
theorem rawBlock_suffixShift_after {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ)
    (j a m : ℕ) (h : a+m≤N) (hcut : j≤a) (lam : ℝ) :
    rawBlock (rawSuffixShift T j lam) a m h=rawBlock T a m h-lam • 1 := by
  -- The actual contiguous embedding determines whether each true diagonal index is shifted.
  ext i k
  change T _ _-(Matrix.diagonal (fun q : Fin N => if j ≤ q.val then lam else 0)) _ _=
    T _ _-lam*(if i=k then 1 else 0)
  dsimp only
  by_cases hik : i=k
  · subst k
    simp [show j ≤ a+i.val by omega]
  · rw [Matrix.diagonal_apply_ne _ (by intro he; apply hik; apply Fin.ext; have hval := congrArg Fin.val he; dsimp only at hval; omega),
      ite_eq_right hik,mul_zero]

/-- Two consecutive actual suffix shifts differ by precisely one physical diagonal-row update.
Use: extend the genuine shifted suffix one site toward the beginning.
Article: main_krylov, apF:twotail.
Proof: compare the changed diagonal site and the remaining entries; away
from that site the two actual suffix membership predicates agree. -/
theorem rawSuffixShift_row {n : ℕ} (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (s : Fin (n+1)) (lam : ℝ) :
    rawSuffixShift T s.val lam=(rawSuffixShift T (s.val+1) lam).updateRow s
      (rawSuffixShift T (s.val+1) lam s+(-lam) • Pi.single s 1) := by
  -- Only the cutoff site changes; all other real diagonal membership decisions coincide.
  ext i j
  by_cases hi : i=s
  · subst i
    by_cases hj : j=s
    · subst j
      simp [Matrix.updateRow_apply,rawSuffixShift,sub_eq_add_neg]
    · simp [Matrix.updateRow_apply,rawSuffixShift,Matrix.diagonal_apply_ne _ (Ne.symm hj),hj]
  · rw [Matrix.updateRow_apply,ite_eq_right hi]
    by_cases hij : i=j
    · subst j
      have hc : (s.val ≤ i.val) ↔ s.val+1 ≤ i.val := by
        have hn : s.val≠i.val := by intro he; exact hi (Fin.ext he.symm)
        omega
      simp only [rawSuffixShift,Matrix.sub_apply,Matrix.diagonal_apply_eq,hc]
    · simp only [rawSuffixShift,Matrix.sub_apply,Matrix.diagonal_apply_ne _ hij,sub_zero]

/-- Extending the actual shifted suffix changes its real determinant by the printed leading-times-tail cofactor.
Use: this is the exact one-site determinant increment behind the actual injection continuation.
Article: main_krylov, apF:twotail.
Proof: apply the true single-diagonal multilinearity identity, factor the
actual tridiagonal minor, and identify its unchanged leading and fully
shifted trailing physical blocks. -/
theorem rawSuffixShift_det_step {n : ℕ} (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (htri : ∀ i j : Fin (n+1), i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (s : Fin (n+1)) (lam : ℝ) :
    (rawSuffixShift T s.val lam).det=(rawSuffixShift T (s.val+1) lam).det-
      lam*(rawBlock T 0 s.val (by omega)).det*
        (rawBlock T (s.val+1) (n-s.val) (by omega)-lam • 1).det := by
  rw [rawSuffixShift_row,det_diagonal_row,
    raw_minor_det _ (rawSuffixShift_tridiagonal T htri _ lam) s,
    rawBlock_suffixShift_before T _ _ _ (by omega) (by omega) lam,
    rawBlock_suffixShift_after T _ _ _ (by omega) le_rfl lam]
  ring


/-- Shifting the actual empty suffix leaves the physical matrix unchanged.
Use: initialize the continuation telescope, including dimension zero.
Article: main_krylov, apF:twotail.
Proof: every genuine matrix index lies strictly below the full dimension. -/
theorem rawSuffixShift_terminal {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (lam : ℝ) :
    rawSuffixShift T N lam=T := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [rawSuffixShift,not_le.mpr i.isLt]
  · simp [rawSuffixShift,Matrix.diagonal_apply_ne _ hij]

/-- Shifting the actual whole suffix is the genuine full scalar matrix shift.
Use: the initial continuation agrees with the true terminal residual determinant.
Article: main_krylov, apF:twotail.
Proof: every genuine index belongs to the suffix beginning at zero. -/
theorem rawSuffixShift_zero {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (lam : ℝ) :
    rawSuffixShift T 0 lam=T-lam • 1 := by
  ext i j
  by_cases hij : i=j
  · subst j; simp [rawSuffixShift]
  · simp [rawSuffixShift,hij]

/-- The sum of the actual independent-injection responses equals the normalized true suffix-shifted physical determinant.
Use: proves the source continuation formula for every supplied positive negative-offdiagonal tridiagonal matrix, including both endpoint cutoffs and empty matrices.
Article: main_krylov, prop:dict(i) and apF:twotail.
Proof: telescope the true diagonal cofactor increments from the actual
empty suffix backward. The proved genuine injection determinant formula
identifies each increment, with the actual positive terminal determinant
providing the real normalization. -/
theorem raw_continuation_eval {N : ℕ} (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (j : ℕ) (hj : j≤N) (lam : ℝ) :
    (rawSuffixShift T j lam).det/T.det=1+lam*∑ s∈Finset.Ico j N,
      (injectionPolynomial ((rawJacobi T).realization dictionaryInterval) N s).eval lam := by
  -- Decreasing induction adds the true diagonal sites in the source chronological continuation order.
  induction hj using Nat.decreasingInduction with
  | self => rw [rawSuffixShift_terminal]; simp [hT.det_pos.ne']
  | of_succ j hj ih =>
    cases N with
    | zero => omega
    | succ n =>
      have hinj := raw_injection_eval T hT htri hneg j hj lam
      rw [rawBlock_shifted_det_congr T (j+1) (n+1-(j+1)) (n-j) (by omega) (by omega) (by omega) lam] at hinj
      have he : (rawSuffixShift T j lam).det/T.det=
          (rawSuffixShift T (j+1) lam).det/T.det+
            lam*(injectionPolynomial ((rawJacobi T).realization dictionaryInterval) (n+1) j).eval lam := by
        rw [rawSuffixShift_det_step T htri ⟨j,hj⟩ lam,hinj]
        ring
      rw [he,ih,Finset.sum_eq_sum_Ico_succ_bot hj]
      ring

end
end krylov.Realization
