import krylov.Design.ChebyshevMajorant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

/-!
Article: main_krylov, lem:chebyshev-design.
Use: construct the actual Hoel--Levine probability design and prove attainment
of the universal Chebyshev bound.
Source: Hoel--Levine (1964), Greenbaum (1979); mathlib supplies Lagrange
interpolation and the actual cosine extrema, including their alternating signs.
-/

namespace krylov.Design
noncomputable section
open Polynomial MeasureTheory jacobi.Finite
open scoped BigOperators InnerProductSpace

/-- The physical Lobatto point, in increasing spectral order.
Article: main_krylov, lem:chebyshev-design. -/
def lobattoNode (I : chebyshev1.SpectralInterval) (m i : ℕ) : ℝ :=
  (I.L + I.mu - I.delta * Polynomial.Chebyshev.node m i) / 2

/-- The exterior Lagrange coefficient in the standard Chebyshev coordinate.
Article: main_krylov, lem:chebyshev-design. -/
def lobattoCoefficient (I : chebyshev1.SpectralInterval) (m i : ℕ) : ℝ :=
  (Lagrange.basis (Finset.range (m + 1)) (Polynomial.Chebyshev.node m) i).eval I.eta

/-- Every constructed Lobatto point belongs to the original spectral interval.
Article: main_krylov, lem:chebyshev-design.
Proof: the cosine coordinate lies in the closed unit interval. -/
theorem lobattoNode_mem (I : chebyshev1.SpectralInterval) (m i : ℕ) :
    lobattoNode I m i ∈ Set.Icc I.mu I.L := by
  obtain ⟨hlo, hhi⟩ := Polynomial.Chebyshev.node_mem_Icc (n := m) (i := i)
  have hd := I.delta_pos
  dsimp [lobattoNode, chebyshev1.SpectralInterval.delta] at *
  constructor <;> nlinarith

/-- The actual Lobatto points are distinct, including the degree-zero singleton.
Article: main_krylov, lem:chebyshev-design.
Proof: strict decrease of the cosine extrema and the positive spectral width. -/
theorem lobattoNode_injective (I : chebyshev1.SpectralInterval) (m : ℕ) :
    Function.Injective (fun i : Fin (m + 1) => lobattoNode I m i.val) := by
  intro i j hij
  apply Fin.ext
  apply (Polynomial.Chebyshev.strictAntiOn_node m).injOn
    (by simpa using i.isLt) (by simpa using j.isLt)
  dsimp [lobattoNode] at hij
  have hd := I.delta_pos
  nlinarith

/-- The normalized affine spectral coordinate maps each Lobatto point back to its cosine.
Article: main_krylov, lem:chebyshev-design. -/
theorem z_lobattoNode (I : chebyshev1.SpectralInterval) (m i : ℕ) :
    I.z (lobattoNode I m i) = Polynomial.Chebyshev.node m i := by
  dsimp [chebyshev1.SpectralInterval.z, lobattoNode]
  field_simp [ne_of_gt I.delta_pos]
  ring

/-- The normalized Chebyshev residual alternates with constant modulus at the actual nodes.
Article: main_krylov, lem:chebyshev-design. -/
theorem residual_lobattoNode (I : chebyshev1.SpectralInterval) (m i : ℕ) (hi : i ≤ m) :
    (I.residual m).eval (lobattoNode I m i) = (-1 : ℝ) ^ i / I.den m := by
  rw [I.residual_eval, z_lobattoNode,
    Polynomial.Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr hi)]

/-- Exterior Lagrange coefficients have exactly the alternating Chebyshev signs.
Article: main_krylov, lem:chebyshev-design.
Proof: all exterior numerator factors are positive; mathlib gives the signed denominator product. -/
theorem lobattoCoefficient_sign (I : chebyshev1.SpectralInterval) (m i : ℕ) (hi : i ≤ m) :
    0 < (-1 : ℝ) ^ i * lobattoCoefficient I m i := by
  have hn : 0 < ∏ j ∈ (Finset.range (m + 1)).erase i,
      (I.eta - Polynomial.Chebyshev.node m j) := by
    apply Finset.prod_pos
    intro j _
    exact sub_pos.mpr (lt_of_le_of_lt (Real.cos_le_one _) I.eta_gt_one)
  have hd := Polynomial.Chebyshev.zero_lt_prod_node_sub_node hi
  have he : lobattoCoefficient I m i =
      (∏ j ∈ (Finset.range (m + 1)).erase i,
        (I.eta - Polynomial.Chebyshev.node m j)) *
      (∏ j ∈ (Finset.range (m + 1)).erase i,
        (Polynomial.Chebyshev.node m i - Polynomial.Chebyshev.node m j))⁻¹ := by
    simp only [lobattoCoefficient, Lagrange.basis, eval_prod, Lagrange.basisDivisor,
      eval_mul, eval_C, eval_sub, eval_X, Finset.prod_mul_distrib,
      ← Finset.prod_inv_distrib]
    ring
  rw [he]
  have hs := inv_pos.mpr hd
  rw [mul_inv, ← inv_pow, inv_neg_one] at hs
  nlinarith [mul_pos hn hs]

/-- Absolute Lagrange coefficients equal their signed values, with no zero coefficient.
Article: main_krylov, lem:chebyshev-design. -/
theorem abs_lobattoCoefficient (I : chebyshev1.SpectralInterval) (m i : ℕ) (hi : i ≤ m) :
    |lobattoCoefficient I m i| = (-1 : ℝ) ^ i * lobattoCoefficient I m i := by
  calc
    _ = |(-1 : ℝ) ^ i * lobattoCoefficient I m i| := by simp
    _ = _ := abs_of_pos (lobattoCoefficient_sign I m i hi)

/-- Lagrange interpolation at the exterior point for a polynomial in the physical coordinate.
Article: main_krylov, lem:chebyshev-design.
Proof: compose with the affine inverse coordinate, interpolate at the cosine extrema, and evaluate. -/
theorem lobatto_interpolation (I : chebyshev1.SpectralInterval) (m : ℕ)
    (p : ℝ[X]) (hp : p.natDegree ≤ m) :
    ∑ i : Fin (m + 1), lobattoCoefficient I m i.val * p.eval (lobattoNode I m i.val) =
      p.eval 0 := by
  let A : ℝ[X] := C ((I.L + I.mu) / 2) - C (I.delta / 2) * X
  have hA : A.natDegree ≤ 1 := by
    exact (natDegree_sub_le _ _).trans (max_le (by simp) (by
      simpa using (natDegree_C_mul_le (I.delta / 2) (X : ℝ[X]))))
  have hdeg : (p.comp A).degree < (Finset.range (m + 1)).card := by
    apply lt_of_le_of_lt degree_le_natDegree
    rw [Finset.card_range, Nat.cast_lt]
    have hc := natDegree_comp_le (p := p) (q := A)
    have hmul : p.natDegree * A.natDegree ≤ m := by
      nlinarith
    exact Nat.lt_succ_of_le (hc.trans hmul)
  have he := congrArg (fun q : ℝ[X] => q.eval I.eta)
    (Lagrange.eq_interpolate (Polynomial.Chebyshev.strictAntiOn_node m).injOn hdeg)
  have hz : A.eval I.eta = 0 := by
    dsimp [A, chebyshev1.SpectralInterval.eta]
    simp only [eval_sub, eval_C, eval_mul, eval_X]
    field_simp [ne_of_gt I.delta_pos]
    ring
  rw [Fin.sum_univ_eq_sum_range (fun i => lobattoCoefficient I m i * p.eval (lobattoNode I m i))]
  rw [eval_comp, hz] at he
  rw [he]
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C, eval_comp,
    lobattoCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  have ha : A.eval (Polynomial.Chebyshev.node m i) = lobattoNode I m i := by
    simp only [A, eval_sub, eval_C, eval_mul, eval_X, lobattoNode]
    ring
  rw [ha]
  ring

/-- The sum of absolute exterior Lagrange coefficients is the exact Chebyshev denominator.
Article: main_krylov, lem:chebyshev-design.
Proof: interpolate the alternating normalized residual at its exterior normalization point. -/
theorem sum_abs_lobattoCoefficient (I : chebyshev1.SpectralInterval) (m : ℕ) :
    ∑ i : Fin (m + 1), |lobattoCoefficient I m i.val| = I.den m := by
  have he := lobatto_interpolation I m (I.residual m) (I.residual_natDegree m).le
  have hp : (I.residual m).eval 0 = 1 := (chebyshevCompetitor I m).property.2
  rw [hp] at he
  have he' : (∑ i : Fin (m + 1), |lobattoCoefficient I m i.val|) / I.den m = 1 := by
    rw [Finset.sum_div]
    convert! he using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [residual_lobattoNode I m i.val (by omega), abs_lobattoCoefficient I m i.val (by omega)]
    ring
  exact (div_eq_one_iff_eq (I.den_ne m)).mp he'

/-- The constructed exterior coefficients are precisely the physical Lagrange values at zero.
Article: main_krylov, lem:chebyshev-design.
Proof: every normalized linear Lagrange factor is invariant under the affine spectral coordinate. -/
theorem lobattoCoefficient_physical (I : chebyshev1.SpectralInterval) (m i : ℕ) (hi : i ≤ m) :
    lobattoCoefficient I m i =
      (Lagrange.basis (Finset.range (m + 1)) (lobattoNode I m) i).eval 0 := by
  simp only [lobattoCoefficient, Lagrange.basis, eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  obtain ⟨hji, hjm⟩ := Finset.mem_erase.mp hj
  have hz : Polynomial.Chebyshev.node m i - Polynomial.Chebyshev.node m j ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    exact hji ((Polynomial.Chebyshev.strictAntiOn_node m).injOn
      (by simpa using Nat.lt_succ_of_le (Finset.mem_range_succ_iff.mp hjm))
      (by simpa using Nat.lt_succ_of_le hi) he.symm)
  have hp : lobattoNode I m i - lobattoNode I m j ≠ 0 := by
    have he : lobattoNode I m i - lobattoNode I m j =
        -(I.delta / 2) * (Polynomial.Chebyshev.node m i - Polynomial.Chebyshev.node m j) := by
      simp only [lobattoNode]
      ring
    rw [he]
    exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (ne_of_gt I.delta_pos) (by norm_num))) hz
  simp only [Lagrange.basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  rw [← div_eq_inv_mul, ← div_eq_inv_mul]
  apply (div_eq_div_iff (by simpa only [ne_eq] using hz) hp).mpr
  dsimp [lobattoNode, chebyshev1.SpectralInterval.eta]
  field_simp [ne_of_gt I.delta_pos]
  ring

/-- The actual positive Hoel--Levine discrete probability measure.
Its masses are proportional to the absolute exterior Lagrange coefficients.
Article: main_krylov, lem:chebyshev-design. -/
def lobattoMeasure (I : chebyshev1.SpectralInterval) (m : ℕ) : DiscreteMeasure (m + 1) where
  node i := lobattoNode I m i.val
  distinct := lobattoNode_injective I m
  weight i := |lobattoCoefficient I m i.val| / I.den m
  positive i := div_pos (by
    rw [abs_lobattoCoefficient I m i.val (by omega)]
    exact lobattoCoefficient_sign I m i.val (by omega)) (I.den_pos m)
  probability := by
    rw [← Finset.sum_div, sum_abs_lobattoCoefficient, div_self (I.den_ne m)]

/-- The Hoel--Levine design as a genuine probability measure on the original interval.
Article: main_krylov, lem:chebyshev-design. -/
def lobattoProbability (I : chebyshev1.SpectralInterval) (m : ℕ) :
    ProbabilityMeasure (Spectrum I) :=
  atomicProbability (lobattoMeasure I m)
    (fun i => ⟨lobattoNode I m i.val, lobattoNode_mem I m i.val⟩)

end
end krylov.Design
