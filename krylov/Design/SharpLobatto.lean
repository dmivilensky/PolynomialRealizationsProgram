import krylov.Design.Lobatto

/-!
Article: main_krylov, lem:chebyshev-design, and the mixed Chebyshev lower majorant.
Use: prove that the explicitly constructed positive probability measure attains
the sharp all-measures extremum, then use monotonicity for the mixed criterion.
Source: Hoel--Levine (1964), Greenbaum (1979). The proof uses genuine polynomial
integration, exterior interpolation, and completion of the square.
-/

/-!
Article: krylov, Lemma D.2 [lem:chebyshev-design].

The physical Lobatto design with absolute Lagrange weights attains the universal Christoffel
maximum, and its residual equals the sech expression.
The result holds also at degree zero in Lean; the article restricts m≥1.
-/

namespace krylov.Design
noncomputable section
open Polynomial MeasureTheory jacobi.Finite
open scoped BigOperators InnerProductSpace

/-- At each atom, the signed residual cancels the sign of its exterior interpolation coefficient.
Article: main_krylov, lem:chebyshev-design. -/
theorem lobatto_weight_residual (I : chebyshev1.SpectralInterval) (m : ℕ)
    (i : Fin (m + 1)) :
    (lobattoMeasure I m).weight i * (I.residual m).eval (lobattoNode I m i.val) =
      lobattoCoefficient I m i.val / (I.den m) ^ 2 := by
  change |lobattoCoefficient I m i.val| / I.den m * _ = _
  rw [abs_lobattoCoefficient I m i.val (by omega),
    residual_lobattoNode I m i.val (by omega)]
  have hs : (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ i.val = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((-1 : ℝ) ^ i.val * (-1 : ℝ) ^ i.val) *
        lobattoCoefficient I m i.val / I.den m ^ 2 := by ring
    _ = _ := by rw [hs, one_mul]

/-- The residual is orthogonal to every normalized variation, in actual finite spectral L2.
Article: main_krylov, lem:chebyshev-design.
Proof: exterior Lagrange interpolation after the exact signed-weight cancellation. -/
theorem lobatto_residual_pairing (I : chebyshev1.SpectralInterval) (m : ℕ)
    (p : ℝ[X]) (hp : p.natDegree ≤ m) :
    ∑ i : Fin (m + 1), (lobattoMeasure I m).weight i *
      (I.residual m).eval (lobattoNode I m i.val) * p.eval (lobattoNode I m i.val) =
      (I.epsilon m) ^ 2 * p.eval 0 := by
  simp_rw [lobatto_weight_residual, div_mul_eq_mul_div]
  rw [← Finset.sum_div, lobatto_interpolation I m p hp]
  simp only [chebyshev1.SpectralInterval.epsilon]
  ring

/-- Polynomial energy against the actual Lobatto probability is its positive weighted spectral sum.
Article: main_krylov, lem:chebyshev-design. -/
theorem polynomialEnergy_lobatto (I : chebyshev1.SpectralInterval) (m : ℕ) (p : ℝ[X]) :
    polynomialEnergy (spectralCoordinate I) (lobattoProbability I m) p =
      ∑ i : Fin (m + 1), (lobattoMeasure I m).weight i *
        (p.eval (lobattoNode I m i.val)) ^ 2 := by
  rw [lobattoProbability, polynomialEnergy_atomic _ _ _ (fun _ => rfl),
    ← real_inner_self_eq_norm_sq, DiscreteMeasure.inner_evaluate]
  apply Finset.sum_congr rfl
  intro i _
  change (lobattoMeasure I m).weight i * p.eval (lobattoNode I m i.val) *
    p.eval (lobattoNode I m i.val) = _
  ring

/-- The actual Chebyshev residual has its sharp constant energy on the Lobatto design.
Article: main_krylov, lem:chebyshev-design. -/
theorem polynomialEnergy_lobatto_residual (I : chebyshev1.SpectralInterval) (m : ℕ) :
    polynomialEnergy (spectralCoordinate I) (lobattoProbability I m) (I.residual m) =
      (I.epsilon m) ^ 2 := by
  rw [polynomialEnergy_lobatto]
  have he := lobatto_residual_pairing I m (I.residual m) (I.residual_natDegree m).le
  have hp : (I.residual m).eval 0 = 1 := (chebyshevCompetitor I m).property.2
  rw [hp, mul_one] at he
  convert! he using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [pow_two, mul_assoc]

/-- Completion of the square proves the genuine Christoffel minimum at the constructed design.
Article: main_krylov, lem:chebyshev-design.
Proof: the nonnegative squared normalized variation has zero residual cross term. -/
theorem polynomialEnergy_lobatto_lower (I : chebyshev1.SpectralInterval) (m : ℕ)
    (p : Competitor m 0) :
    (I.epsilon m) ^ 2 ≤ polynomialEnergy (spectralCoordinate I) (lobattoProbability I m) p.val := by
  have hn : 0 ≤ polynomialEnergy (spectralCoordinate I) (lobattoProbability I m)
      (p.val - I.residual m) := polynomialEnergy_nonneg _ _ _
  have hc := lobatto_residual_pairing I m p.val p.property.1
  rw [p.property.2, mul_one] at hc
  have hr := polynomialEnergy_lobatto_residual I m
  rw [polynomialEnergy_lobatto] at hn hr ⊢
  have he : (∑ i : Fin (m + 1), (lobattoMeasure I m).weight i *
        ((p.val - I.residual m).eval (lobattoNode I m i.val)) ^ 2) =
      (∑ i : Fin (m + 1), (lobattoMeasure I m).weight i *
        (p.val.eval (lobattoNode I m i.val)) ^ 2) -
      2 * (∑ i : Fin (m + 1), (lobattoMeasure I m).weight i *
        (I.residual m).eval (lobattoNode I m i.val) * p.val.eval (lobattoNode I m i.val)) +
      ∑ i : Fin (m + 1), (lobattoMeasure I m).weight i *
        ((I.residual m).eval (lobattoNode I m i.val)) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [eval_sub]
    ring
  rw [he, hc, hr] at hn
  linarith

/-- The explicitly constructed Hoel--Levine design attains the sharp Chebyshev information.
Article: main_krylov, lem:chebyshev-design, the attaining half of the exact extremum. -/
theorem christoffel_lobatto (I : chebyshev1.SpectralInterval) (m : ℕ) :
    christoffel m 0 (spectralCoordinate I) (lobattoProbability I m) = (I.epsilon m) ^ 2 := by
  apply le_antisymm (christoffel_le_chebyshev I m _)
  exact le_ciInf (polynomialEnergy_lobatto_lower I m)

/-- The exact sharp all-probability-measures maximum, with its explicit attaining measure.
Article: main_krylov, lem:chebyshev-design.
Proof: combine the genuine universal majorant and the constructed design equality. -/
theorem chebyshev_design_extremum (I : chebyshev1.SpectralInterval) (m : ℕ) :
    (∀ ν : ProbabilityMeasure (Spectrum I),
      christoffel m 0 (spectralCoordinate I) ν ≤ (I.epsilon m) ^ 2) ∧
    christoffel m 0 (spectralCoordinate I) (lobattoProbability I m) = (I.epsilon m) ^ 2 :=
  ⟨christoffel_le_chebyshev I m, christoffel_lobatto I m⟩

/-- Each prefix of the mixed objective has the article's constructive Chebyshev lower bound.
Article: main_krylov, the mixed lower majorant following thm:B.
Proof: use the degree-k Lobatto design and information monotonicity in every earlier degree. -/
theorem intervalObjective_half_lobatto_lower (I : chebyshev1.SpectralInterval) (M k : ℕ)
    (w : Fin M → ℝ) (hw : ∀ i, 0 ≤ w i) :
    I.epsilon k * ∑ i ∈ Finset.univ.filter (fun i : Fin M => i.val + 1 ≤ k), w i ≤
      intervalObjective I M w (1 / 2) (lobattoProbability I k) := by
  unfold intervalObjective mixedObjective
  rw [Finset.mul_sum]
  apply le_trans _ (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (fun i : Fin M => i.val + 1 ≤ k) Finset.univ) ?_)
  · apply Finset.sum_le_sum
    intro i hi
    have hik := (Finset.mem_filter.mp hi).2
    have hinfo := christoffel_antitone_degree hik 0 (spectralCoordinate I) (lobattoProbability I k)
    rw [christoffel_lobatto I k] at hinfo
    have hs : I.epsilon k ≤ Real.sqrt
        (christoffel (i.val + 1) 0 (spectralCoordinate I) (lobattoProbability I k)) := by
      apply (Real.le_sqrt (chebyshev_scale_pos I k).le
        (christoffel_nonneg _ _ _ _)).mpr
      exact hinfo
    rw [← Real.sqrt_eq_rpow]
    exact (mul_comm _ _).trans_le (mul_le_mul_of_nonneg_left hs (hw i))
  · intro i _ _
    exact mul_nonneg (hw i) (Real.rpow_nonneg (christoffel_nonneg _ _ _ _) _)

end
end krylov.Design
