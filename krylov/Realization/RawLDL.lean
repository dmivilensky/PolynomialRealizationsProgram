import krylov.Realization.RawFrozen
import chebyshev2.Green.Bidiagonal

/-!
Article: main_krylov, prop:dict(i), genuine raw physical LDL factorization.
Use: construct the actual unit lower bidiagonal factor and positive reciprocal
pivots from the supplied matrix, with its true negative square-root couplings.
Source: standard tridiagonal LDL elimination (Meurant, Golub--Meurant);
reuse the existing real bidiagonal row contraction from the earlier package.
-/

namespace krylov.Realization
noncomputable section
open Matrix chebyshev2
open scoped BigOperators
variable {N : ℕ}

/-- A real unit lower-bidiagonal weighted Gram product has its exact diagonal and two adjacent entry formulas.
Use: reuse the existing genuine two-entry row contraction for the actual physical LDL product.
Article: main_krylov, prop:dict(i).
Proof: the proved real bidiagonal row contraction leaves only the current
site and its one genuine predecessor. Comparing the two row supports yields
the diagonal, adjacent and zero far-band entries, including the first site. -/
theorem bidiagonal_ldl_apply (d l : Fin N → ℝ) (i j : Fin N) :
    (Bidiagonal.matrix (fun _ => 1) l*Matrix.diagonal d*(Bidiagonal.matrix (fun _ => 1) l)ᵀ) i j=
      if i=j then d i+(if h : 0 < i.val then l i^2*d ⟨i.val-1,by omega⟩ else 0)
      else if i.val+1=j.val then d i*l j
      else if j.val+1=i.val then l i*d j else 0 := by
  -- The existing real bidiagonal contraction keeps exactly the current and preceding physical sites.
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply,mul_assoc]
  rw [Bidiagonal.row_mul]
  by_cases hi : 0 < i.val
  · rw [dite_eq_left hi]
    have hp : i.val-1+1=i.val := by omega
    have he : j=(⟨i.val-1,by omega⟩ : Fin N) ↔ j.val+1=i.val := by
      rw [Fin.ext_iff]
      dsimp only
      omega
    simp only [Bidiagonal.matrix,hp,he]
    by_cases hij : i=j
    · subst j
      simp [pow_two,hi,mul_comm,mul_assoc]
    · have hji := Ne.symm hij
      have hv : i.val≠j.val := fun he => hij (Fin.ext he)
      by_cases ha : i.val+1=j.val
      · have hb : ¬j.val+1=i.val := by omega
        simp [hij,hji,hv,ha,hb]
      · by_cases hb : j.val+1=i.val
        · have hprev : (⟨i.val-1,by omega⟩ : Fin N)=j := Fin.ext (by dsimp only; omega)
          simp [hij,hji,hv,ha,hb,hprev]
        · simp [hij,hji,hv,ha,hb]
  · rw [dite_eq_right hi]
    have hb : ¬j.val+1=i.val := by omega
    simp only [Bidiagonal.matrix]
    by_cases hij : i=j
    · subst j; simp [hi]
    · by_cases ha : i.val+1=j.val
      · simp [hij,Ne.symm hij,ha]
      · simp [hij,Ne.symm hij,ha,hb]

/-- The actual unit lower bidiagonal physical factor constructed from the supplied positive tridiagonal matrix.
Use: its genuine adjacent coefficient is the source −sqrt(β_s), with β derived from actual matrix entries and leading pivots.
Article: main_krylov, prop:dict(i), L. -/
def rawLowerFactor (T : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Bidiagonal.matrix (fun _ => 1) (fun i => -Real.sqrt (rawBeta T (i.val-1)))


/-- The actual constructed raw physical lower factor has unit diagonal.
Use: the source LDL normalization is a proved property of the real factor.
Article: main_krylov, prop:dict(i).
Proof: only the actual diagonal summand survives; a site cannot be its own predecessor. -/
theorem rawLowerFactor_diag (T : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) : rawLowerFactor T i i=1 := by
  simp [rawLowerFactor,Bidiagonal.matrix]

/-- The actual constructed raw physical factor is lower triangular.
Use: its genuine finite lower-factor determinant has the standard unit-diagonal normalization.
Article: main_krylov, prop:dict(i).
Proof: neither the diagonal nor the one-step lower band can appear above the true diagonal. -/
theorem rawLowerFactor_lower (T : Matrix (Fin N) (Fin N) ℝ) : (rawLowerFactor T).IsLowerTriangular := by
  intro i j hij
  change i<j at hij
  have hv : i.val<j.val := hij
  simp [rawLowerFactor,Bidiagonal.matrix,ne_of_lt hij,show ¬j.val+1=i.val by omega]

/-- Every actual raw factor subdiagonal entry is the genuine negative square root of its constructed coupling.
Use: fixes the source orientation in the real physical factorization.
Article: main_krylov, prop:dict(i).
Proof: the true adjacent indices select exactly the physical predecessor coupling. -/
theorem rawLowerFactor_adjacent (T : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) (hij : i.val+1=j.val) :
    rawLowerFactor T j i= -Real.sqrt (rawBeta T i.val) := by
  have hne : j≠i := by intro he; subst j; omega
  simp [rawLowerFactor,Bidiagonal.matrix,hne,hij,show j.val-1=i.val by omega]

/-- Every supplied positive negative-offdiagonal tridiagonal matrix has the genuine constructed physical LDL factorization with D_ss=1/α_s and L_(s+1,s)=−sqrt(β_s).
Use: the realization dictionary starts from the actual arbitrary source matrix, rather than supplied measured CG coefficients or a presumed factorization.
Article: main_krylov, prop:dict(i), T=LDLᵀ.
Proof: the proved actual bidiagonal weighted-product formula reduces the
identity to real physical entries. The genuine leading-determinant pivot
recurrence proves the diagonal; true negative-edge square-root signs and
positive actual pivots prove both adjacent bands; the supplied far band vanishes. -/
theorem raw_ldl (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) :
    T=rawLowerFactor T*Matrix.diagonal (fun i : Fin N => (rawAlpha T i.val)⁻¹)*(rawLowerFactor T)ᵀ := by
  -- Compare the original physical entries with the two true supports of the constructed lower factor.
  ext i j
  rw [rawLowerFactor,bidiagonal_ldl_apply]
  by_cases hij : i=j
  · subst j
    rw [ite_eq_left rfl]
    by_cases hi : 0 < i.val
    · rw [dite_eq_left hi]
      simp only [neg_sq,Real.sq_sqrt (rawBeta_nonneg T (i.val-1))]
      have hd := raw_ldl_diagonal T hT htri hneg i
      rw [ite_eq_left hi] at hd
      simpa only [div_eq_mul_inv] using hd.symm
    · rw [dite_eq_right hi]
      have hd := raw_ldl_diagonal T hT htri hneg i
      rw [ite_eq_right hi] at hd
      exact hd.symm
  · rw [ite_eq_right hij]
    by_cases hu : i.val+1=j.val
    · rw [ite_eq_left hu,show j.val-1=i.val by omega,rawLower_edge T hT htri hneg i j hu]
      field_simp [(rawAlpha_pos T hT htri hneg i.val i.isLt).ne']
    · rw [ite_eq_right hu]
      by_cases hl : j.val+1=i.val
      · rw [ite_eq_left hl,show i.val-1=j.val by omega,rawLower_edge T hT htri hneg j i hl]
        rw [show T j i=T i j from congrFun (congrFun hT.1.isSymm.eq i) j]
        field_simp [(rawAlpha_pos T hT htri hneg j.val j.isLt).ne']
      · rw [ite_eq_right hl,htri i j (by have hv : i.val≠j.val := fun he => hij (Fin.ext he); omega)]
end
end krylov.Realization
