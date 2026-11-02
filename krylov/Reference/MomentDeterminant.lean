import krylov.Reference.Christoffel
import jacobi.Finite.Schur

/-!
Article: Lemma B.6 [lem:chris] of krylov.tex.
Use: identify the exterior minimum with the actual moment Schur complement
and determinant ratio, reusing jacobi's proved inverse Gram projection.
Source: the classical Gram determinant formula for Christoffel functions
(GolubMeurant10), proved here by the Schur determinant identity.
-/

namespace krylov.Reference
noncomputable section
open Matrix Polynomial jacobi.Finite
open scoped BigOperators InnerProductSpace

/-- The augmented Gram matrix, ordered as the constant vector followed by the shifted monomials.
Use: its polynomial specialization is H⁽⁰⁾_(m+1), with an explicit equivalent sum indexing.
Article: main_krylov, lem:chris, the numerator moment determinant. -/
def augmentedGram {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Fin m → E) (v : E) : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) ℝ :=
  Matrix.gram ℝ (Sum.elim (fun _ : Fin 1 => v) f)

/-- The augmented Gram determinant is its principal determinant times the actual squared Schur residual.
Use: gives the printed ratio without introducing a formal matrix inverse as an unverified projection.
Article: main_krylov, lem:chris, Gram Schur determinant identity.
Proof: apply the community block determinant theorem to the positive Gram block;
the one-by-one complement is exactly the already proved jacobi projection complement. -/
theorem augmentedGram_det {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Fin m → E} (hf : LinearIndependent ℝ f) (v : E) :
    (augmentedGram f v).det=(Matrix.gram ℝ f).det*Gram.complement f v := by
  -- The principal inverse exists because the actual vectors are linearly independent.
  let G := Matrix.gram ℝ f
  let A : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => inner ℝ v v
  let B : Matrix (Fin 1) (Fin m) ℝ := fun _ i => inner ℝ v (f i)
  let C : Matrix (Fin m) (Fin 1) ℝ := fun i _ => inner ℝ (f i) v
  let : Invertible G := Matrix.invertibleOfIsUnitDet G
    (isUnit_iff_ne_zero.mpr (Matrix.posDef_gram_of_linearIndependent hf).det_pos.ne')
  have hblock : augmentedGram f v=Matrix.fromBlocks A B C G := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [hblock, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv, Matrix.det_fin_one]
  congr 1
  change inner ℝ v v-(B*G⁻¹*C) 0 0=inner ℝ v v-∑ i, Gram.coefficients f v i*inner ℝ (f i) v
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ v (f i)*(∑ j, G⁻¹ i j*inner ℝ (f j) v)=
    (∑ j, G⁻¹ i j*inner ℝ (f j) v)*inner ℝ (f i) v
  rw [real_inner_comm v (f i)]
  exact mul_comm _ _

/-- The actual Schur residual minimizes distance among all combinations of the preceding vectors.
Use: proves the Christoffel minimum using the independently verified inverse Gram projection.
Article: main_krylov, lem:chris, Schur complement as the minimum.
Proof: every competitor differs from the true residual by a vector in the
preceding span, so the proved Gram orthogonality gives Pythagoras. -/
theorem gram_complement_minimum {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Fin m → E} (hf : LinearIndependent ℝ f) (v : E) (c : Fin m → ℝ) :
    Gram.complement f v≤‖v-∑ i, c i • f i‖^2 := by
  -- Compare to the actual residual, not just to a solution of a formal normal equation.
  let w := ∑ i, (Gram.coefficients f v i-c i) • f i
  have ho : inner ℝ (Gram.residual f v) w=0 := by
    simp only [w, inner_sum, real_inner_smul_right]
    apply Finset.sum_eq_zero
    intro i _
    rw [real_inner_comm (f i) (Gram.residual f v), Gram.residual_orthogonal hf v i, mul_zero]
  have he : v-∑ i, c i • f i=Gram.residual f v+w := by
    dsimp only [Gram.residual, w]
    simp only [sub_smul, Finset.sum_sub_distrib]
    abel
  rw [he, norm_add_sq_real, ho, Gram.residual_norm_sq hf]
  nlinarith [sq_nonneg ‖w‖]

/-- Shifted monomial evaluation vectors in the actual spectral L² space.
Use: their Gram matrix is exactly H⁽²⁾_m.
Article: main_krylov, lem:chris, positive shifted moment matrix. -/
def shiftedMonomials {N : ℕ} (M : DiscreteMeasure N) (m : ℕ) : Fin m → EuclideanSpace ℝ (Fin N) :=
  fun i => M.evaluate (X^(i.val+1))

/-- The shifted monomial Gram block is genuinely positive definite up to the number of positive atoms.
Use: justifies the inverse and denominator in the printed moment-determinant formula, including m=N.
Article: main_krylov, lem:chris, H⁽²⁾_m positive definite.
Proof: multiply the already proved full Vandermonde evaluation basis by the
invertible positive node diagonal and restrict to the requested prefix. -/
theorem shiftedMonomials_independent {N : ℕ} (M : DiscreteMeasure N) (hn : ∀ i, 0<M.node i)
    {m : ℕ} (hm : m≤N) : LinearIndependent ℝ (shiftedMonomials M m) := by
  -- Positive nodes preserve evaluation independence even when the shifted degree reaches N.
  let D : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N) :=
    { toFun v := WithLp.toLp 2 (fun i => M.node i*v i)
      map_add' u v := by ext i; simp only [PiLp.add_apply, mul_add]
      map_smul' a v := by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have hD : Function.Injective D := by
    intro u v h
    ext i
    have he := congrArg (fun w : EuclideanSpace ℝ (Fin N) => w i) h
    exact mul_left_cancel₀ (hn i).ne' he
  have hli := (M.evaluate_linearIndependent (fun i : Fin N => (X^i.val : ℝ[X]))
    (fun _ => by simp) (fun _ => by simp)).map' D (LinearMap.ker_eq_bot.mpr hD)
  have hp := hli.comp (Fin.castLE hm) (Fin.castLE_injective hm)
  convert hp using 1
  funext i
  ext j
  change Real.sqrt (M.weight j)*(X^(i.val+1) : ℝ[X]).eval (M.node j)=
    M.node j*(Real.sqrt (M.weight j)*(X^i.val : ℝ[X]).eval (M.node j))
  simp only [eval_pow, eval_X, pow_succ, eval_mul]
  ring

/-- The actual exterior Schur polynomial computed from the shifted moment inverse.
Use: constructs an attaining admissible polynomial independently of the reproducing kernel.
Article: main_krylov, lem:chris, p=1+tq and the moment normal equations. -/
def momentPolynomial {N : ℕ} (M : DiscreteMeasure N) (m : ℕ) : ℝ[X] :=
  1-∑ i : Fin m, Gram.coefficients (shiftedMonomials M m) (M.evaluate 1) i • X^(i.val+1)

/-- The moment polynomial has exactly the actual inverse-Gram residual as its evaluation vector.
Use: its squared norm is the actual Schur complement already proved in jacobi.
Article: main_krylov, lem:chris.
Proof: weighted evaluation commutes with the finite polynomial combination. -/
theorem evaluate_momentPolynomial {N : ℕ} (M : DiscreteMeasure N) (m : ℕ) :
    M.evaluate (momentPolynomial M m)=Gram.residual (shiftedMonomials M m) (M.evaluate 1) := by
  change M.evaluation (1-∑ i : Fin m, _ • _)=_
  rw [map_sub, map_sum]
  simp only [map_smul]
  rfl

/-- The constructed moment polynomial is normalized and obeys its required degree bound.
Use: the Schur minimum is attained within the actual Christoffel admissible set.
Article: main_krylov, lem:chris, normalized degree-m minimizer.
Proof: all correction terms contain X and have degree at most m. -/
theorem momentPolynomial_admissible {N : ℕ} (M : DiscreteMeasure N) (m : ℕ) :
    (momentPolynomial M m).natDegree≤m ∧ (momentPolynomial M m).eval 0=1 := by
  -- The constant coefficient is untouched; every remaining degree is a shifted monomial degree.
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    simp only [momentPolynomial, coeff_sub, finsetSum_coeff, coeff_smul, smul_eq_mul]
    rw [coeff_one, ite_eq_right (by omega : k≠0)]
    have hs : (∑ i : Fin m, Gram.coefficients (shiftedMonomials M m) (M.evaluate 1) i*
        (X^(i.val+1) : ℝ[X]).coeff k)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [coeff_eq_zero_of_natDegree_lt (by simp only [natDegree_X_pow]; omega), mul_zero]
    rw [hs, sub_self]
  · simp only [momentPolynomial, eval_sub, eval_one, eval_finsetSum, eval_smul, eval_pow, eval_X, eval_mul,
      pow_succ, mul_zero, smul_zero, Finset.sum_const_zero, sub_zero]

/-- Every normalized degree-m polynomial is a constant minus a combination of the actual shifted monomials.
Use: proves the Schur comparison for the whole admissible class, not only a proposed optimizer.
Article: main_krylov, lem:chris, p=1+tq.
Proof: expand the polynomial through degree m and separate its normalized constant coefficient. -/
theorem normalized_monomial_expansion {p : ℝ[X]} {m : ℕ} (hp : p.natDegree≤m) (h0 : p.eval 0=1) :
    p=1-∑ i : Fin m, (-p.coeff (i.val+1)) • X^(i.val+1) := by
  have he := p.as_sum_range_C_mul_X_pow' (by omega : p.natDegree<m+1)
  rw [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ] at he
  have hc : p.coeff 0=1 := by rw [coeff_zero_eq_eval_zero]; exact h0
  simpa only [Fin.val_zero, pow_zero, hc, C_1, one_mul, Fin.val_succ, neg_smul,
    Finset.sum_neg_distrib, sub_neg_eq_add, smul_eq_C_mul] using he

/-- The actual Schur complement equals the exterior Christoffel minimum.
Use: closes the moment/kernel normalization bridge before taking determinants.
Article: main_krylov, lem:chris, μ₀−bᵀ(H⁽²⁾_m)⁻¹b.
Proof: the moment polynomial is admissible and has the Schur residual energy;
the independent Gram minimum bounds the actual kernel optimizer in the other direction. -/
theorem moment_complement_christoffel {N : ℕ} (M : DiscreteMeasure N) (hn : ∀ i, 0<M.node i)
    {m : ℕ} (hm : m<N) :
    Gram.complement (shiftedMonomials M m) (M.evaluate 1)=(christoffelKernel M m 0)⁻¹ := by
  -- Both independent attaining constructions are compared over the entire normalized polynomial class.
  have hli := shiftedMonomials_independent M hn hm.le
  have ha := momentPolynomial_admissible M m
  have hlow := (christoffel_minimum_unique M hm 0 ha.1 ha.2).1
  rw [evaluate_momentPolynomial, Gram.residual_norm_sq hli] at hlow
  have hopt := christoffelPolynomial_admissible M m 0
  have hexp := normalized_monomial_expansion hopt.1 hopt.2
  have hu := gram_complement_minimum hli (M.evaluate 1)
    (fun i => -(christoffelPolynomial M m 0).coeff (i.val+1))
  have heval : (M.evaluate 1-∑ i : Fin m, (-(christoffelPolynomial M m 0).coeff (i.val+1)) • shiftedMonomials M m i)=
      M.evaluate (christoffelPolynomial M m 0) := by
    nth_rw 2 [hexp]
    change M.evaluation 1-∑ i : Fin m, _ • M.evaluation _=M.evaluation _
    rw [map_sub, map_sum]
    simp only [map_smul]
  rw [heval, christoffelPolynomial_norm M hm 0] at hu
  exact le_antisymm hu hlow

/-- The exterior Christoffel minimum is the exact ratio of the actual augmented and shifted moment determinants.
Use: this is the article's determinant formula with proved positive denominator.
Article: main_krylov, lem:chris, λ_m(0)=det H⁽⁰⁾_(m+1)/det H⁽²⁾_m.
Proof: divide the actual augmented Gram determinant identity by its positive principal determinant. -/
theorem christoffel_moment_determinant {N : ℕ} (M : DiscreteMeasure N) (hn : ∀ i, 0<M.node i)
    {m : ℕ} (hm : m<N) :
    (christoffelKernel M m 0)⁻¹=
      (augmentedGram (shiftedMonomials M m) (M.evaluate 1)).det/(Matrix.gram ℝ (shiftedMonomials M m)).det := by
  have hli := shiftedMonomials_independent M hn hm.le
  have hd := (Matrix.posDef_gram_of_linearIndependent hli).det_pos.ne'
  rw [augmentedGram_det hli, moment_complement_christoffel M hn hm, mul_div_cancel_left₀ _ hd]

/-- The printed shifted moment entries are exactly the actual shifted-monomial Gram entries.
Use: identifies the denominator matrix with H⁽²⁾_m rather than only an abstract Gram construction.
Article: main_krylov, lem:chris, (H⁽²⁾_m)_ij=∫t^(i+j+2)dν.
Proof: weighted polynomial evaluation and the exponent addition rule identify each summand. -/
theorem shifted_moment_entry {N m : ℕ} (M : DiscreteMeasure N) (i j : Fin m) :
    Matrix.gram ℝ (shiftedMonomials M m) i j=
      ∑ k, M.weight k*(M.node k)^(i.val+j.val+2) := by
  rw [Matrix.gram_apply, shiftedMonomials, shiftedMonomials, M.inner_evaluate]
  apply Finset.sum_congr rfl
  intro k _
  simp only [eval_pow, eval_X]
  rw [mul_assoc, ← pow_add]
  congr 2
  omega

/-- The augmented moment indexing places the constant first and then degrees one through m.
Use: records the exact ordering of H⁽⁰⁾_(m+1) in the determinant formula.
Article: main_krylov, lem:chris, moment numerator indexing. -/
def momentIndex {m : ℕ} : Fin 1 ⊕ Fin m → ℕ := Sum.elim (fun _ => 0) (fun i => i.val+1)

/-- Every augmented entry is the printed unshifted moment of the sum of its two degrees.
Use: the ratio theorem uses exactly H⁽⁰⁾_(m+1), with a proved indexing bridge.
Article: main_krylov, lem:chris, (H⁽⁰⁾_(m+1))_ij=∫t^(i+j)dν.
Proof: its actual evaluation vectors are the monomials of the stated degree; multiply their scalar powers. -/
theorem augmented_moment_entry {N m : ℕ} (M : DiscreteMeasure N) (i j : Fin 1 ⊕ Fin m) :
    augmentedGram (shiftedMonomials M m) (M.evaluate 1) i j=
      ∑ k, M.weight k*(M.node k)^(momentIndex i+momentIndex j) := by
  -- The sum indexing is translated to the exact monomial degree before evaluating its Gram entry.
  have hv (a : Fin 1 ⊕ Fin m) : Sum.elim (fun _ : Fin 1 => M.evaluate 1) (shiftedMonomials M m) a=
      M.evaluate (X^momentIndex a) := by
    cases a with
    | inl a => simp only [momentIndex, Sum.elim_inl, pow_zero]
    | inr a => rfl
  change inner ℝ (Sum.elim (fun _ : Fin 1 => M.evaluate 1) (shiftedMonomials M m) i)
    (Sum.elim (fun _ : Fin 1 => M.evaluate 1) (shiftedMonomials M m) j)=_
  rw [hv, hv, M.inner_evaluate]
  apply Finset.sum_congr rfl
  intro k _
  simp only [eval_pow, eval_X, mul_assoc, pow_add]

end
end krylov.Reference
