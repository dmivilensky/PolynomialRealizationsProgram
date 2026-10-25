import chebyshev2.Continuum.FiniteFredholm

/-!
Article: chebyshev2, Proposition 3.
Logarithmic determinant update in finite rank.
Use: `chebyshev2.Continuum.finite_rankOne_logDeterminant` feeds
`chebyshev2.Continuum.rankOne_logDeterminant` (The Fredholm matrix determinant lemma for the
already defined spectral logarithm of the actual compact operator).
Proof chain: `chebyshev2.Comparison.Profile.signed_determinant_comparison` — chebyshev2,
Theorem 3.4; Signed determinant and square-trace comparisons.
-/
namespace chebyshev2.Continuum
noncomputable section
open Real
open scoped InnerProductSpace BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `InnerProductSpace.rankOne ℝ (sqrt c • v) (sqrt c • v) = c •
InnerProductSpace.rankOne ℝ v v`.

Use: `chebyshev2.Continuum.finite_rankOne_logDeterminant` rewrites with this identity to
establish exact identity `logDeterminant D.eigenvalue s = (∑ i, log (1+s/2*e i))+ log
(1+s/2*u*(‖v‖^2-∑ i, (s/2)*e i/(1+s/2*e i)*(inner ℝ (b i) v)^2))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem rankOne_sqrt (c : ℝ) (hc : 0 ≤ c) (v : FeatureSpace) :
    InnerProductSpace.rankOne ℝ (sqrt c • v) (sqrt c • v) =
      c • InnerProductSpace.rankOne ℝ v v := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  apply ContinuousLinearMap.ext
  intro z
  change inner ℝ (sqrt c • v) z • (sqrt c • v) = c • (inner ℝ v z • v)
  rw [real_inner_smul_left,smul_smul,smul_smul]
  congr 1
  linear_combination inner ℝ v z * (sq_sqrt hc)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/--
Defines `extendedFamily` of type `ι ⊕ Unit → FeatureSpace` by `Sum.elim (fun i => sqrt (e i) •
b i) (fun _ => sqrt u • v)`.

Use: `chebyshev2.Continuum.extendedFamily_det` rewrites with this definition to establish
the identity stated in that declaration.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.
-/
def extendedFamily (b : ι → FeatureSpace) (e : ι → ℝ) (u : ℝ) (v : FeatureSpace) :
    ι ⊕ Unit → FeatureSpace := Sum.elim (fun i => sqrt (e i) • b i) (fun _ => sqrt u • v)

/--
Finite-dimensional Schur complement, with an additional vector that need not belong to the span
of the orthonormal family.

Exact identity `Matrix.det ((1 : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)+a • Matrix.of (fun i j =>
inner ℝ (extendedFamily b e u v i) (extendedFamily b e u v j))) = (∏ i, (1+a*e i)) *
(1+a*u*(‖v‖^2- ∑ i, a*e i/(1+a*e i)*(inner ℝ (b i) v)^2))`.

Use: `chebyshev2.Continuum.finite_rankOne_logDeterminant` rewrites with this identity to
establish exact identity `logDeterminant D.eigenvalue s = (∑ i, log (1+s/2*e i))+ log
(1+s/2*u*(‖v‖^2-∑ i, (s/2)*e i/(1+s/2*e i)*(inner ℝ (b i) v)^2))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Separate `i=j` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Identify the summands/integrands on their required domain before replacing the sum
or integral. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem extendedFamily_det (b : ι → FeatureSpace) (hb : Orthonormal ℝ b)
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) {u a : ℝ} (hu : 0 ≤ u) (ha : 0 ≤ a)
    (v : FeatureSpace) :
    Matrix.det ((1 : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)+a •
      Matrix.of (fun i j => inner ℝ (extendedFamily b e u v i) (extendedFamily b e u v j))) =
      (∏ i, (1+a*e i)) * (1+a*u*(‖v‖^2-
        ∑ i, a*e i/(1+a*e i)*(inner ℝ (b i) v)^2)) := by
  -- Separate `i=j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  let A : Matrix ι ι ℝ := Matrix.diagonal (fun i => 1+a*e i)
  let B : Matrix ι Unit ℝ := fun i _ => a*sqrt (e i)*sqrt u*inner ℝ (b i) v
  let C : Matrix Unit ι ℝ := fun _ i => a*sqrt (e i)*sqrt u*inner ℝ (b i) v
  let Q : Matrix Unit Unit ℝ := fun _ _ => 1+a*u*‖v‖^2
  have hpos (i : ι) : 0 < 1+a*e i := by nlinarith [he i]
  let : Invertible A := Matrix.invertibleOfIsUnitDet A (by
    change IsUnit (Matrix.diagonal (fun i => 1+a*e i)).det
    rw [Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => (hpos i).ne')))
  have hblock : ((1 : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ)+a •
      Matrix.of (fun i j => inner ℝ (extendedFamily b e u v i) (extendedFamily b e u v j))) =
        Matrix.fromBlocks A B C Q := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · by_cases hij : i=j
      · subst j
        simp only [Matrix.add_apply,Matrix.one_apply_eq,Matrix.smul_apply,smul_eq_mul,
          Matrix.of_apply,extendedFamily,Sum.elim_inl,
          real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _),
          hb.norm_eq_one,mul_one,Matrix.fromBlocks_apply₁₁,
          A,Matrix.diagonal_apply_eq]
        nlinarith [sq_sqrt (he i)]
      · simp [Matrix.add_apply,extendedFamily,
          real_inner_smul_left,real_inner_smul_right,hb.inner_eq_zero hij,A,hij]
    · simp only [Matrix.add_apply,Matrix.one_apply,Sum.inl_ne_inr,ite_false,
        Matrix.smul_apply,smul_eq_mul,Matrix.of_apply,extendedFamily,Sum.elim_inl,Sum.elim_inr,
        real_inner_smul_left,real_inner_smul_right,zero_add,Matrix.fromBlocks_apply₁₂,B]
      ring
    · simp only [Matrix.add_apply,Matrix.one_apply,Sum.inr_ne_inl,ite_false,
        Matrix.smul_apply,smul_eq_mul,Matrix.of_apply,extendedFamily,Sum.elim_inl,Sum.elim_inr,
        real_inner_smul_left,real_inner_smul_right,zero_add,Matrix.fromBlocks_apply₂₁,C]
      rw [real_inner_comm (b j) v]
      ring
    · have hij : i=j := Subsingleton.elim _ _
      subst j
      simp only [Matrix.add_apply,Matrix.one_apply_eq,Matrix.smul_apply,smul_eq_mul,
        Matrix.of_apply,extendedFamily,Sum.elim_inr,
        real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _),
        Matrix.fromBlocks_apply₂₂,Q]
      rw [mul_pow,sq_sqrt hu]
      ring
  rw [hblock,Matrix.det_fromBlocks₁₁,Matrix.invOf_eq_nonsing_inv,
    Matrix.det_unique (Q-C*A⁻¹*B)]
  rw [show A.det=∏ i, (1+a*e i) by dsimp only [A]; rw [Matrix.det_diagonal]]
  congr 1
  change 1+a*u*‖v‖^2-(C*A⁻¹*B) (():Unit) (():Unit) = _
  have hAi : A⁻¹=Matrix.diagonal (fun i => (1+a*e i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    dsimp only [A]
    rw [Matrix.diagonal_mul_diagonal', ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hpos i).ne'
  have hmul : (C*A⁻¹*B) (():Unit) (():Unit) =
      a*u*∑ i, a*e i/(1+a*e i)*(inner ℝ (b i) v)^2 := by
    rw [hAi,Matrix.mul_apply]
    simp only [Matrix.mul_diagonal,C,B]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (a*sqrt (e i)*sqrt u*inner ℝ (b i) v)*(1+a*e i)⁻¹*
      (a*sqrt (e i)*sqrt u*inner ℝ (b i) v) = _
    field_simp [(hpos i).ne']
    calc
      _ = a^2*(sqrt (e i))^2*(sqrt u)^2*(inner ℝ (b i) v)^2 := by ring
      _ = _ := by rw [sq_sqrt (he i),sq_sqrt hu]; ring
  rw [hmul]
  ring

omit [DecidableEq ι] in
/--
The stated quantitative bound `0 ≤ ‖v‖^2-∑ i, a*e i/(1+a*e i)*(inner ℝ (b i) v)^2`.

Use: `chebyshev2.Continuum.finite_rankOne_logDeterminant` uses this bound to establish
exact identity `logDeterminant D.eigenvalue s = (∑ i, log (1+s/2*e i))+ log (1+s/2*u*(‖v‖^2-∑
i, (s/2)*e i/(1+s/2*e i)*(inner ℝ (b i) v)^2))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem finite_resolvent_remainder_nonneg (b : ι → FeatureSpace) (hb : Orthonormal ℝ b)
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) {a : ℝ} (ha : 0 ≤ a) (v : FeatureSpace) :
    0 ≤ ‖v‖^2-∑ i, a*e i/(1+a*e i)*(inner ℝ (b i) v)^2 := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hB := hb.sum_inner_products_le v (s := Finset.univ)
  simp only [Real.norm_eq_abs,sq_abs] at hB
  have hsum : (∑ i, a*e i/(1+a*e i)*(inner ℝ (b i) v)^2) ≤
      ∑ i, (inner ℝ (b i) v)^2 := by
    apply Finset.sum_le_sum
    intro i _
    have hden : 0 < 1+a*e i := by nlinarith [he i]
    exact mul_le_of_le_one_left (sq_nonneg _) ((div_le_one hden).mpr (by linarith))
  linarith

/--
Logarithmic determinant update in finite rank. The extra direction is retained even if the
original operator vanishes on it.

Exact identity `logDeterminant D.eigenvalue s = (∑ i, log (1+s/2*e i))+ log (1+s/2*u*(‖v‖^2-∑
i, (s/2)*e i/(1+s/2*e i)*(inner ℝ (b i) v)^2))`.

Use: `chebyshev2.Continuum.rankOne_logDeterminant` uses this identity to establish exact
identity `logDeterminant D'.eigenvalue s = logDeterminant D.eigenvalue s+ log (1+s/2*u*inner ℝ
v (inverseOfUnit _ (positive_pencil_unit hp (show 0 ≤ s/2 by positivity)) v))`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem finite_rankOne_logDeterminant (b : ι → FeatureSpace) (hb : Orthonormal ℝ b)
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s)
    (v : FeatureSpace)
    (D : PositiveSpectralData ((∑ i, e i • InnerProductSpace.rankOne ℝ (b i) (b i))+
      u • InnerProductSpace.rankOne ℝ v v)) :
    logDeterminant D.eigenvalue s = (∑ i, log (1+s/2*e i))+
      log (1+s/2*u*(‖v‖^2-∑ i, (s/2)*e i/(1+s/2*e i)*(inner ℝ (b i) v)^2)) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hfamily : (∑ i, InnerProductSpace.rankOne ℝ
      (extendedFamily b e u v i) (extendedFamily b e u v i)) =
      (∑ i, e i • InnerProductSpace.rankOne ℝ (b i) (b i))+
        u • InnerProductSpace.rankOne ℝ v v := by
    rw [Fintype.sum_sum_type]
    simp only [extendedFamily,Sum.elim_inl,Sum.elim_inr,rankOne_sqrt _ hu,
      Finset.sum_const,Finset.card_univ,Fintype.card_unique,one_nsmul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact rankOne_sqrt _ (he i) _
  rw [familyGram_logDeterminant_of_eq D _ hfamily hs,
    extendedFamily_det b hb e he hu (div_nonneg hs (by norm_num)) v]
  have hp : 0 < ∏ i, (1+s/2*e i) :=
    Finset.prod_pos (fun i _ => by nlinarith [he i])
  have hq := finite_resolvent_remainder_nonneg b hb e he (a := s/2)
    (div_nonneg hs (by norm_num)) v
  have hd : 0 < 1+s/2*u*(‖v‖^2-∑ i, (s/2)*e i/(1+s/2*e i)*(inner ℝ (b i) v)^2) := by
    have ha : 0 ≤ s/2*u := mul_nonneg (div_nonneg hs (by norm_num)) hu
    nlinarith [mul_nonneg ha hq]
  rw [log_mul hp.ne' hd.ne',Real.log_prod (fun i _ => by nlinarith [he i])]

end
end chebyshev2.Continuum
