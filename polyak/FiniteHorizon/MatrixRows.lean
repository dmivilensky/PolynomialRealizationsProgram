import polyak.FiniteHorizon.FactorizationGram
import polyak.FiniteHorizon.ZeroSymbol

/-!
Article: Appendix C, dense matrices and triangular diagonal rows.
Use: the actual lag-{2,3,5} certificates have width seven, hence eight
coordinates. The exact finite rearrangement below needs no matrix symmetry.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Energy
open scoped BigOperators

abbrev WindowMatrix7 := Fin 8 → Fin 8 → ℝ

/-- Zero extension of an eight-coordinate matrix to natural coordinate indices. -/
def matrixEntry7 (C : WindowMatrix7) (a b : ℕ) : ℝ :=
  if ha : a<8 then if hb : b<8 then C ⟨a,ha⟩ ⟨b,hb⟩ else 0 else 0

/-- Diagonal rows of the full quadratic form, retaining both off-diagonal entries. -/
def matrixRows7 (C : WindowMatrix7) (e a : ℕ) : ℝ :=
  if e=0 then matrixEntry7 C a a
  else matrixEntry7 C a (a+e)+matrixEntry7 C (a+e) a

private def symmetricValue7 (H : WindowMatrix7) (a b : Fin 8) : ℝ :=
  if a≤b then H a b else H b a

/-- Exact finite rearrangement into diagonal rows for every symmetric pairing. -/
theorem matrixRows7_pairing (C H : WindowMatrix7) (hH : ∀ a b, H a b=H b a) :
    (∑ a, ∑ b, C a b*H a b)=
      ∑ e ∈ Finset.range 8, ∑ a ∈ Finset.range (8-e),
        matrixRows7 C e a*matrixEntry7 H a (a+e) := by
  have hcanon (a b : Fin 8) : H a b=symmetricValue7 H a b := by
    unfold symmetricValue7
    split_ifs
    · rfl
    · exact hH a b
  conv_lhs =>
    arg 2
    ext a
    arg 2
    ext b
    rw [hcanon a b]
  simp only [matrixEntry7] 
  simp_rw [hcanon]
  norm_num [Fin.sum_univ_succ,Finset.sum_range_succ,matrixRows7,matrixEntry7,symmetricValue7]
  ring

/-- The dense quadratic window on an arbitrary real Hilbert sequence. -/
def matrixEval7 (C : WindowMatrix7) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : ℤ → E) (j : ℤ) : ℝ :=
  ∑ a, ∑ b, C a b*inner ℝ (f (j+(a : ℤ))) (f (j+(b : ℤ)))

theorem matrixEval7_eq_rows (C : WindowMatrix7) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : ℤ → E) (j : ℤ) :
    matrixEval7 C f j=
      ∑ e ∈ Finset.range 8, ∑ a ∈ Finset.range (8-e),
        matrixRows7 C e a*diagonalValue f e (j+a) := by
  have he:=matrixRows7_pairing C
    (fun a b => inner ℝ (f (j+(a : ℤ))) (f (j+(b : ℤ))))
    (fun a b => real_inner_comm _ _)
  change matrixEval7 C f j=_ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro a ha
  have ha' : a<8:=by have h:=Finset.mem_range.mp ha; omega
  have hb' : a+e<8:=by have h:=Finset.mem_range.mp ha; have h':=Finset.mem_range.mp he; omega
  simp only [matrixEntry7,dite_eq_left ha',dite_eq_left hb',diagonalValue]
  push_cast
  rw [add_assoc]

/-- Exact agreement of the dense Fourier symbol and the triangular-row symbol. -/
theorem coefficientSymbol_eq_rowSymbol7 (C : WindowMatrix7) (θ : FrequencyCircle) :
    coefficientSymbol C θ=rowSymbol 7 (matrixRows7 C) θ := by
  have hchar (a b : Fin 8) :
      (character ((a : ℤ)-(b : ℤ)) θ).re=(character ((b : ℤ)-(a : ℤ)) θ).re := by
    rw [show (a : ℤ)-(b : ℤ)= -((b : ℤ)-(a : ℤ)) by ring,fourier_neg]
    rfl
  have he:=matrixRows7_pairing C
    (fun a b => (character ((a : ℤ)-(b : ℤ)) θ).re) hchar
  change coefficientSymbol C θ=_ at he
  rw [he]
  unfold rowSymbol
  change _=∑ e : Fin 8, (fun e : ℕ =>
    (∑ a ∈ Finset.range (7-e+1), matrixRows7 C e a)*(character (e : ℤ) θ).re) e
  rw [←Finset.sum_range (n:=8) (fun e : ℕ =>
    (∑ a ∈ Finset.range (7-e+1), matrixRows7 C e a)*(character (e : ℤ) θ).re)]
  apply Finset.sum_congr rfl
  intro e he
  have he' : e<8:=Finset.mem_range.mp he
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by congr 1; omega)
  intro a ha
  have ha' : a<8:=by have h:=Finset.mem_range.mp ha; omega
  have hb' : a+e<8:=by have h:=Finset.mem_range.mp ha; omega
  simp only [matrixEntry7,dite_eq_left ha',dite_eq_left hb']
  have hdiff : (a : ℤ)-((a+e : ℕ) : ℤ)= -(e : ℤ):=by push_cast; ring
  rw [hdiff,fourier_neg]
  rfl

theorem matrixEntry7_abs (C : WindowMatrix7) (a b : ℕ) :
    matrixEntry7 (fun i j => |C i j|) a b=|matrixEntry7 C a b| := by
  unfold matrixEntry7
  split_ifs <;> simp

/-- Off-diagonal coalescing does not increase the total absolute coefficient mass. -/
theorem matrixRows7_mass_le (C : WindowMatrix7) :
    (∑ e ∈ Finset.range 8, ∑ a ∈ Finset.range (8-e), |matrixRows7 C e a|)≤
      ∑ a, ∑ b, |C a b| := by
  have he:=matrixRows7_pairing (fun a b => |C a b|) (fun _ _ => 1) (fun _ _ => rfl)
  simp only [mul_one] at he
  have hmass : (∑ a, ∑ b, |C a b|)=
      ∑ e ∈ Finset.range 8, ∑ a ∈ Finset.range (8-e),
        matrixRows7 (fun i j => |C i j|) e a := by
    rw [he]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro a ha
    have ha' : a<8:=by have h:=Finset.mem_range.mp ha; omega
    have hb' : a+e<8:=by have h:=Finset.mem_range.mp ha; have h':=Finset.mem_range.mp he; omega
    simp only [matrixEntry7,dite_eq_left ha',dite_eq_left hb',mul_one]
  rw [hmass]
  apply Finset.sum_le_sum
  intro e _
  apply Finset.sum_le_sum
  intro a _
  unfold matrixRows7
  split_ifs
  · exact le_of_eq (matrixEntry7_abs C a a).symm
  · rw [matrixEntry7_abs,matrixEntry7_abs]
    exact abs_add_le _ _

/-- Explicit absolute coefficient size of the local row primitive. -/
def rowPrimitiveSize (D : ℕ) (μ : ℕ → ℕ → ℝ) (d : ℕ → ℝ) : ℝ :=
  (∑ e ∈ Finset.range (D+1), primitiveSize (D-e) (μ e))+primitiveSize D d

theorem rowPrimitiveSize_le (D : ℕ) (μ : ℕ → ℕ → ℝ) (d : ℕ → ℝ) :
    rowPrimitiveSize D μ d≤(D : ℝ)*
      ((∑ e ∈ Finset.range (D+1), ∑ a ∈ Finset.range (D-e+1), |μ e a|)+
        ∑ a ∈ Finset.range (D+1), |d a|) := by
  have hrows : (∑ e ∈ Finset.range (D+1), primitiveSize (D-e) (μ e))≤
      (D : ℝ)*(∑ e ∈ Finset.range (D+1), ∑ a ∈ Finset.range (D-e+1), |μ e a|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    apply (primitiveSize_le (D-e) (μ e)).trans
    have hc : ((D-e : ℕ) : ℝ)≤(D : ℝ):=by exact_mod_cast Nat.sub_le D e
    exact mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun a _ => abs_nonneg _)
  unfold rowPrimitiveSize
  calc
    _≤(D : ℝ)*(∑ e ∈ Finset.range (D+1), ∑ a ∈ Finset.range (D-e+1), |μ e a|)+
        (D : ℝ)*(∑ a ∈ Finset.range (D+1), |d a|) :=
      add_le_add hrows (primitiveSize_le D d)
    _=_ :=by ring

theorem matrixRows7_primitiveSize_le (C : WindowMatrix7) (d : ℕ → ℝ) :
    rowPrimitiveSize 7 (matrixRows7 C) d≤7*
      ((∑ a, ∑ b, |C a b|)+∑ a ∈ Finset.range 8, |d a|) := by
  apply (rowPrimitiveSize_le 7 (matrixRows7 C) d).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ)≤7)
  apply add_le_add _ le_rfl
  calc
    _=(∑ e ∈ Finset.range 8, ∑ a ∈ Finset.range (8-e), |matrixRows7 C e a|) :=by
      apply Finset.sum_congr rfl
      intro e he
      have h:=Finset.mem_range.mp he
      have heq : 7-e+1=8-e:=by omega
      rw [heq]
    _≤_:=matrixRows7_mass_le C

/-- The explicit primitive size controls its value on every bounded local input. -/
theorem primitive_abs_le (D : ℕ) (μ : ℕ → ℝ) (f : ℤ → ℝ) (j : ℤ) (R : ℝ)
    (hf : ∀ r : ℕ, r<D → |f (j+r)|≤R) :
    |primitive D μ f j|≤primitiveSize D μ*R := by
  have hp (a : ℕ) (ha : a∈Finset.range (D+1)) : |prefixSum f j a|≤(a : ℝ)*R := by
    unfold prefixSum
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _≤∑ r ∈ Finset.range a, R:=by
        apply Finset.sum_le_sum
        intro r hr
        exact hf r (by have h₁:=Finset.mem_range.mp ha; have h₂:=Finset.mem_range.mp hr; omega)
      _=_:=by simp
  unfold primitive primitiveSize
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _≤∑ a ∈ Finset.range (D+1), |μ a| *((a : ℝ)*R) :=by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hp a ha) (abs_nonneg _)
    _=_:=by simp_rw [←mul_assoc]; rw [Finset.sum_mul]

/-- Local coefficient size controls the full quadratic/value primitive. -/
theorem rowPrimitive_abs_le (D : ℕ) (μ : ℕ → ℕ → ℝ) (d : ℕ → ℝ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : ℤ → E) (h : ℤ → ℝ) (j : ℤ) (R : ℝ)
    (hf : ∀ e r : ℕ, e≤D → r<D-e → |diagonalValue f e (j+r)|≤R)
    (hh : ∀ r : ℕ, r<D → |h (j+r)|≤R) :
    |rowPrimitive D μ d f h j|≤rowPrimitiveSize D μ d*R := by
  unfold rowPrimitive rowPrimitiveSize
  apply (abs_add_le _ _).trans
  have hquad : |∑ e ∈ Finset.range (D+1), primitive (D-e) (μ e) (diagonalValue f e) j|≤
      (∑ e ∈ Finset.range (D+1), primitiveSize (D-e) (μ e))*R := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e he
    exact primitive_abs_le (D-e) (μ e) (diagonalValue f e) j R
      (fun r hr => hf e r (by have h:=Finset.mem_range.mp he; omega) hr)
  calc
    _≤(∑ e ∈ Finset.range (D+1), primitiveSize (D-e) (μ e))*R+primitiveSize D d*R :=
      add_le_add hquad (primitive_abs_le D d h j R hh)
    _=_:=by ring

end polyak.FiniteHorizon
