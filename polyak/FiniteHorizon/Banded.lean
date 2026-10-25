import polyak.FiniteHorizon.MatrixRows

/-!
Article: Appendix C, Lemma telescoping for the concrete width-seven symbols.
Use: a proved finite real sum of squared filters gives an exact local Hilbert
identity, a width-six primitive, and a uniform absolute coefficient bound.
The result uses the actual Gram factors, with no assumed energy inequality.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy
open scoped BigOperators

def matrixMass7 (C : WindowMatrix7) : ℝ := ∑ a, ∑ b, |C a b|

theorem matrixMass7_nonneg (C : WindowMatrix7) : 0≤matrixMass7 C := by
  unfold matrixMass7
  positivity

def diagonalMatrix7 (ε : ℝ) (a₀ : Fin 8) : WindowMatrix7 :=
  fun a b => if a=a₀ ∧ b=a₀ then ε else 0

theorem coefficientSymbol_add7 (C B : WindowMatrix7) (θ : FrequencyCircle) :
    coefficientSymbol (fun a b => C a b+B a b) θ=
      coefficientSymbol C θ+coefficientSymbol B θ := by
  unfold coefficientSymbol
  simp_rw [add_mul,Finset.sum_add_distrib]

theorem matrixEval7_add (C B : WindowMatrix7) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : ℤ → E) (j : ℤ) :
    matrixEval7 (fun a b => C a b+B a b) f j=matrixEval7 C f j+matrixEval7 B f j := by
  unfold matrixEval7
  simp_rw [add_mul,Finset.sum_add_distrib]

theorem diagonalMatrix7_symbol (ε : ℝ) (a₀ : Fin 8) (θ : FrequencyCircle) :
    coefficientSymbol (diagonalMatrix7 ε a₀) θ=ε := by
  classical
  simp [coefficientSymbol,diagonalMatrix7,ite_and]

theorem diagonalMatrix7_eval (ε : ℝ) (a₀ : Fin 8) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : ℤ → E) (j : ℤ) :
    matrixEval7 (diagonalMatrix7 ε a₀) f j=ε*‖f (j+(a₀ : ℤ))‖^2 := by
  classical
  simp [matrixEval7,diagonalMatrix7,ite_and]

theorem diagonalMatrix7_mass (ε : ℝ) (a₀ : Fin 8) :
    matrixMass7 (diagonalMatrix7 ε a₀)=|ε| := by
  classical
  unfold matrixMass7 diagonalMatrix7
  have he (a b : Fin 8) : |if a=a₀ ∧ b=a₀ then ε else 0|=
      if a=a₀ ∧ b=a₀ then |ε| else 0 := by split_ifs <;> simp_all
  simp_rw [he]
  simp [ite_and]

theorem matrixMass7_add_le (C B : WindowMatrix7) :
    matrixMass7 (fun a b => C a b+B a b)≤matrixMass7 C+matrixMass7 B := by
  unfold matrixMass7
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun b _ => abs_add_le _ _

/-- Add the actual nonnegative Gram symbol and the chosen diagonal strict gap. -/
def completedMatrix7 (C : WindowMatrix7) {ε : ℝ}
    (cert : GramFactors 7 (fun θ => -coefficientSymbol C θ-ε)) (a₀ : Fin 8) : WindowMatrix7 :=
  fun a b => C a b+cert.matrix a b+diagonalMatrix7 ε a₀ a b

theorem completedMatrix7_symbol_zero (C : WindowMatrix7) {ε : ℝ}
    (cert : GramFactors 7 (fun θ => -coefficientSymbol C θ-ε)) (a₀ : Fin 8)
    (θ : FrequencyCircle) : coefficientSymbol (completedMatrix7 C cert a₀) θ=0 := by
  unfold completedMatrix7
  rw [coefficientSymbol_add7,coefficientSymbol_add7,cert.matrix_symbol,diagonalMatrix7_symbol]
  ring

theorem completedMatrix7_eval (C : WindowMatrix7) {ε : ℝ}
    (cert : GramFactors 7 (fun θ => -coefficientSymbol C θ-ε)) (a₀ : Fin 8)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : ℤ → E) (j : ℤ) :
    matrixEval7 (completedMatrix7 C cert a₀) f j=matrixEval7 C f j+
      (∑ k, ‖∑ a : Fin 8, cert.coefficient k a • f (j+(a : ℤ))‖^2)+
      ε*‖f (j+(a₀ : ℤ))‖^2 := by
  unfold completedMatrix7
  rw [matrixEval7_add,matrixEval7_add,diagonalMatrix7_eval]
  have he:=cert.matrix_eval (fun a : Fin 8 => f (j+(a : ℤ)))
  change matrixEval7 cert.matrix f j=_ at he
  rw [he]

theorem completedMatrix7_mass_le (C : WindowMatrix7) {ε : ℝ} (hε : 0≤ε)
    (cert : GramFactors 7 (fun θ => -coefficientSymbol C θ-ε)) (a₀ : Fin 8) :
    matrixMass7 (completedMatrix7 C cert a₀)≤9*matrixMass7 C+ε := by
  have hGram:=cert.matrix_mass_le_source C hε (fun _ => rfl)
  change matrixMass7 cert.matrix≤(8 : ℕ)*matrixMass7 C at hGram
  unfold completedMatrix7
  calc
    _≤matrixMass7 (fun a b => C a b+cert.matrix a b)+matrixMass7 (diagonalMatrix7 ε a₀) :=
      matrixMass7_add_le _ _
    _≤(matrixMass7 C+matrixMass7 cert.matrix)+ε := by
      rw [diagonalMatrix7_mass,abs_of_nonneg hε]
      exact add_le_add (matrixMass7_add_le _ _) le_rfl
    _≤_ :=by norm_num only [Nat.cast_ofNat] at hGram; linarith

/-- The original dense quadratic and value functional. -/
def bandedFunctional7 (C : WindowMatrix7) (d : ℕ → ℝ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) : ℝ :=
  matrixEval7 C f j+∑ a ∈ Finset.range 8, d a*h (j+a)

theorem rowFunctional_matrix7 (C : WindowMatrix7) (d : ℕ → ℝ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) :
    rowFunctional 7 (matrixRows7 C) d f h j=bandedFunctional7 C d f h j := by
  unfold rowFunctional bandedFunctional7
  rw [matrixEval7_eq_rows]
  congr 1

/-- Lemma telescoping: explicit finite sum-of-squared-filter identity for every
real Hilbert sequence and every integer time, at the actual source width seven. -/
theorem banded_telescoping7 (C : WindowMatrix7) (d : ℕ → ℝ) {ε : ℝ}
    (cert : GramFactors 7 (fun θ => -coefficientSymbol C θ-ε)) (a₀ : Fin 8)
    (hd : ∑ a ∈ Finset.range 8, d a=0) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) :
    bandedFunctional7 C d f h j= -ε*‖f (j+(a₀ : ℤ))‖^2-
      (∑ k, ‖∑ a : Fin 8, cert.coefficient k a • f (j+(a : ℤ))‖^2)+
      rowPrimitive 7 (matrixRows7 (completedMatrix7 C cert a₀)) d f h (j+1)-
      rowPrimitive 7 (matrixRows7 (completedMatrix7 C cert a₀)) d f h j := by
  have hz (θ : FrequencyCircle) : rowSymbol 7 (matrixRows7 (completedMatrix7 C cert a₀)) θ=0 := by
    rw [←coefficientSymbol_eq_rowSymbol7]
    exact completedMatrix7_symbol_zero C cert a₀ θ
  have he:=zero_symbol_telescoping 7 (matrixRows7 (completedMatrix7 C cert a₀)) d hz hd f h j
  rw [rowFunctional_matrix7] at he
  unfold bandedFunctional7 at he ⊢
  rw [completedMatrix7_eval] at he
  linarith

/-- The primitive produced above uses only the seven indices 0,...,6. -/
theorem banded_primitive_local7 (C : WindowMatrix7) (d : ℕ → ℝ) {ε : ℝ}
    (cert : GramFactors 7 (fun θ => -coefficientSymbol C θ-ε)) (a₀ : Fin 8)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f g : ℤ → E) (h k : ℤ → ℝ) (j : ℤ)
    (hf : ∀ r : ℕ, r<7 → f (j+r)=g (j+r))
    (hh : ∀ r : ℕ, r<7 → h (j+r)=k (j+r)) :
    rowPrimitive 7 (matrixRows7 (completedMatrix7 C cert a₀)) d f h j=
      rowPrimitive 7 (matrixRows7 (completedMatrix7 C cert a₀)) d g k j :=
  rowPrimitive_congr _ _ _ _ _ _ _ _ hf hh

/-- Absolute coefficient size of the source functional, including the value charge. -/
def bandedSize7 (C : WindowMatrix7) (d : ℕ → ℝ) : ℝ :=
  matrixMass7 C+∑ a ∈ Finset.range 8, |d a|

/-- The full local primitive bound of Lemma telescoping, with a width-only constant 63. -/
theorem banded_primitiveSize_le7 (C : WindowMatrix7) (d : ℕ → ℝ) {ε : ℝ} (hε : 0≤ε)
    (cert : GramFactors 7 (fun θ => -coefficientSymbol C θ-ε)) (a₀ : Fin 8) :
    rowPrimitiveSize 7 (matrixRows7 (completedMatrix7 C cert a₀)) d≤
      63*(bandedSize7 C d+ε) := by
  have hsize:=matrixRows7_primitiveSize_le (completedMatrix7 C cert a₀) d
  have hmass:=completedMatrix7_mass_le C hε cert a₀
  change rowPrimitiveSize 7 (matrixRows7 (completedMatrix7 C cert a₀)) d≤
    7*(matrixMass7 (completedMatrix7 C cert a₀)+∑ a ∈ Finset.range 8, |d a|) at hsize
  have hd : 0≤∑ a ∈ Finset.range 8, |d a|:=Finset.sum_nonneg fun a _ => abs_nonneg _
  unfold bandedSize7
  nlinarith

/-- A convenient actual functional bound, with the same width-only constant. -/
theorem banded_primitive_abs_le7 (C : WindowMatrix7) (d : ℕ → ℝ) {ε : ℝ} (hε : 0≤ε)
    (cert : GramFactors 7 (fun θ => -coefficientSymbol C θ-ε)) (a₀ : Fin 8)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) {R : ℝ} (hR : 0≤R)
    (hf : ∀ e r : ℕ, e≤7 → r<7-e → |diagonalValue f e (j+r)|≤R)
    (hh : ∀ r : ℕ, r<7 → |h (j+r)|≤R) :
    |rowPrimitive 7 (matrixRows7 (completedMatrix7 C cert a₀)) d f h j|≤
      63*(bandedSize7 C d+ε)*R :=
  (rowPrimitive_abs_le 7 _ d f h j R hf hh).trans
    (mul_le_mul_of_nonneg_right (banded_primitiveSize_le7 C d hε cert a₀) hR)

/-- The exact local primitive at the original arbitrary integer offset. -/
def bandedPrimitive7 (C : WindowMatrix7) (d : ℕ → ℝ) {ε : ℝ}
    (cert : GramFactors 7 (fun θ => -coefficientSymbol C θ-ε)) (a₀ : Fin 8) (o : ℤ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) : ℝ :=
  rowPrimitive 7 (matrixRows7 (completedMatrix7 C cert a₀)) d f h (j+o)

/-- Lemma telescoping with its original arbitrary offset and every integer time. -/
theorem banded_telescoping_offset7 (C : WindowMatrix7) (d : ℕ → ℝ) {ε : ℝ}
    (cert : GramFactors 7 (fun θ => -coefficientSymbol C θ-ε)) (a₀ : Fin 8) (o : ℤ)
    (hd : ∑ a ∈ Finset.range 8, d a=0) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) :
    bandedFunctional7 C d f h (j+o)= -ε*‖f (j+o+(a₀ : ℤ))‖^2-
      (∑ k, ‖∑ a : Fin 8, cert.coefficient k a • f (j+o+(a : ℤ))‖^2)+
      bandedPrimitive7 C d cert a₀ o f h (j+1)-bandedPrimitive7 C d cert a₀ o f h j := by
  unfold bandedPrimitive7
  rw [show j+1+o=j+o+1 by ring]
  exact banded_telescoping7 C d cert a₀ hd f h (j+o)

end polyak.FiniteHorizon
