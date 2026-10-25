import polyak.Boundary.Lag
import polyak.Spectral.Compact

/-!
Article: (dualpoly), Lemma dualfactor and primal–dual optimality.
Use: a finite vector of nonnegative upper-lag weights, paired with lower lag one.
Proof: polynomial divided differences factor the full symbol, including G=c=1;
their positivity gives strict monotonicity in the nonnegative twist.
-/

noncomputable section
open scoped BigOperators
namespace polyak.Boundary
open Spectral Polynomial

/-- Article: finitely supported nonnegative upper-lag weights of total mass one. -/
structure DualWeights where
  /-- Article: selected upper lags J. -/
  lags : Finset ℕ
  /-- Article: only positive lag indices are allowed. -/
  positive_lag : ∀ n ∈ lags, 1 ≤ n
  /-- Article: upper-lag weights. -/
  weight : ℕ → ℝ
  /-- Article: primal inequalities are combined with nonnegative coefficients. -/
  nonneg : ∀ n ∈ lags, 0 ≤ weight n
  /-- Article: unit sum cancels the common normalized value constant. -/
  sum_one : (∑ n ∈ lags, weight n) = 1

/-- Article: Φ=L₁+∑wₙUₙ, with no unverified sign or optimality hypothesis. -/
def dualSymbol (W : DualWeights) (u G c : ℝ) : ℝ :=
  normalizedLower u G 1 c + ∑ n ∈ W.lags, W.weight n*normalizedUpper u G n c

/-- Article: the polynomial α_J of Lemma dualfactor. -/
def alphaPolynomial (W : DualWeights) (G : ℝ) : ℝ[X] :=
  1 + ∑ n ∈ W.lags,
    C (W.weight n/lagDenominator G n)*dividedPolynomial (Polynomial.Chebyshev.T ℝ (n : ℤ)) G

/-- Article: the polynomial β_J of Lemma dualfactor. -/
def betaPolynomial (W : DualWeights) (G : ℝ) : ℝ[X] :=
  ∑ n ∈ W.lags,
    C (W.weight n/lagDenominator G n)*dividedPolynomial (Polynomial.Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)) G

/-- Article: α_J as an evaluated polynomial. -/
def alpha (W : DualWeights) (G c : ℝ) : ℝ := (alphaPolynomial W G).eval c

/-- Article: β_J as an evaluated polynomial. -/
def beta (W : DualWeights) (G c : ℝ) : ℝ := (betaPolynomial W G).eval c

/-- Article: Q is a genuine polynomial, including its continuation through c=G. -/
def dualPolynomial (W : DualWeights) (u G : ℝ) : ℝ[X] :=
  -((1-X^2-C (u^2))*alphaPolynomial W G - C (2*u)*(1-X^2)*betaPolynomial W G)

/-- Article: evaluation of α in its finite divided-difference form. -/
theorem alpha_eq (W : DualWeights) (G c : ℝ) :
    alpha W G c = 1 + ∑ n ∈ W.lags,
      W.weight n/lagDenominator G n*divided (Polynomial.Chebyshev.T ℝ (n : ℤ)) G c := by
  simp [alpha,alphaPolynomial,divided,Polynomial.eval_finsetSum]

/-- Article: evaluation of β in its finite divided-difference form. -/
theorem beta_eq (W : DualWeights) (G c : ℝ) :
    beta W G c = ∑ n ∈ W.lags,
      W.weight n/lagDenominator G n*divided (Polynomial.Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)) G c := by
  simp [beta,betaPolynomial,divided,Polynomial.eval_finsetSum]

/-- Article: α_J≥1 uniformly throughout the compact frequency interval. -/
theorem alpha_ge_one (W : DualWeights) {G : ℝ} (hG : 1 ≤ G) (c : Frequency) :
    1 ≤ alpha W G c := by
  rw [alpha_eq]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun n hn => mul_nonneg
    (div_nonneg (W.nonneg n hn) (lagDenominator_pos hG n (W.positive_lag n hn)).le)
    (divided_T_nonneg n hG c))

/-- Article: β_J≥0 uniformly, including the double endpoint G=c=1. -/
theorem beta_nonneg (W : DualWeights) {G : ℝ} (hG : 1 ≤ G) (c : Frequency) :
    0 ≤ beta W G c := by
  rw [beta_eq]
  exact Finset.sum_nonneg fun n hn => mul_nonneg
    (div_nonneg (W.nonneg n hn) (lagDenominator_pos hG n (W.positive_lag n hn)).le)
    (divided_U_nonneg (n-1) hG c)

/-- Article: L₁ has no denominator and is exactly the first lower constraint. -/
theorem normalizedLower_one (u G c : ℝ) :
    normalizedLower u G 1 c = g u c*(G-c)-2*u*(1-c^2) := by
  simp [normalizedLower,lagDenominator,chebT,chebU,lagB]

/-- Article: one upper lag in divided-difference form. -/
theorem normalizedUpper_factor (u : ℝ) {G : ℝ} (hG : 1 ≤ G) (n : ℕ) (hn : 1 ≤ n) (c : ℝ) :
    normalizedUpper u G n c =
      (G-c)*(g u c*divided (Polynomial.Chebyshev.T ℝ (n : ℤ)) G c/lagDenominator G n-
        2*u*(1-c^2)*divided (Polynomial.Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)) G c/lagDenominator G n)+
        2*u*(1-c^2) := by
  have hD := (lagDenominator_pos hG n hn).ne'
  have hT := divided_factor (Polynomial.Chebyshev.T ℝ (n : ℤ)) G c
  have hU := divided_factor (Polynomial.Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)) G c
  calc
    _ = (g u c*((G-c)*divided (Polynomial.Chebyshev.T ℝ (n : ℤ)) G c)-
        2*u*(1-c^2)*((G-c)*divided (Polynomial.Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)) G c))/
          lagDenominator G n+2*u*(1-c^2) := by
      rw [hT,hU]
      unfold normalizedUpper lagB lagDenominator chebT chebU
      dsimp only [lagDenominator,chebU] at hD
      field_simp [hD]
      ring
    _ = _ := by ring

/-- Article: Lemma dualfactor, full exact polynomial factorization.
Proof: sum the upper divided differences and use the unit sum to cancel d. -/
theorem dual_factor (W : DualWeights) (u : ℝ) {G : ℝ} (hG : 1 ≤ G) (c : ℝ) :
    dualSymbol W u G c =
      (G-c)*(g u c*alpha W G c-2*u*(1-c^2)*beta W G c) := by
  unfold dualSymbol
  rw [normalizedLower_one,alpha_eq,beta_eq]
  have hs : (∑ n ∈ W.lags,W.weight n*normalizedUpper u G n c) =
      (G-c)*(g u c*(∑ n ∈ W.lags,
        W.weight n/lagDenominator G n*divided (Polynomial.Chebyshev.T ℝ (n : ℤ)) G c)-
        2*u*(1-c^2)*(∑ n ∈ W.lags,
          W.weight n/lagDenominator G n*divided (Polynomial.Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)) G c))+
        2*u*(1-c^2) := by
    calc
      _ = ∑ n ∈ W.lags,
          ((G-c)*(g u c*(W.weight n/lagDenominator G n*divided (Polynomial.Chebyshev.T ℝ (n : ℤ)) G c)-
            2*u*(1-c^2)*(W.weight n/lagDenominator G n*divided (Polynomial.Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)) G c))+
            W.weight n*(2*u*(1-c^2))) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [normalizedUpper_factor u hG n (W.positive_lag n hn)]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_sub_distrib,
          ← Finset.mul_sum,← Finset.mul_sum,← Finset.sum_mul,W.sum_one,one_mul]
  rw [hs]
  ring

/-- Article: Q=-Φ/(G−c), expressed as a true polynomial identity with no excluded endpoint. -/
theorem dualPolynomial_factor (W : DualWeights) (u : ℝ) {G : ℝ} (hG : 1 ≤ G) (c : ℝ) :
    dualSymbol W u G c = -(G-c)*(dualPolynomial W u G).eval c := by
  rw [dual_factor W u hG]
  simp [dualPolynomial,alpha,beta,g]
  ring

/-- Article: strict monotonicity estimate of the complete dual symbol in the nonnegative twist. -/
theorem dualSymbol_mono (W : DualWeights) {G u u' : ℝ} (hG : 1 ≤ G)
    (hu : 0 ≤ u) (huu' : u ≤ u') (c : Frequency) :
    dualSymbol W u' G c ≤ dualSymbol W u G c-(G-c)*(u'^2-u^2) := by
  have ha := alpha_ge_one W hG c
  have hb := beta_nonneg W hG c
  have hc : 0 ≤ 1-(c : ℝ)^2 := by
    have hs := (sq_le_one_iff_abs_le_one (c : ℝ)).mpr (abs_le.mpr c.property)
    linarith
  have hgap : 0 ≤ G-(c : ℝ) := sub_nonneg.mpr (c.property.2.trans hG)
  have hd : 0 ≤ u'^2-u^2 := by nlinarith
  have hda : u'^2-u^2 ≤ (u'^2-u^2)*alpha W G c := by nlinarith
  have hdb : 0 ≤ 2*(u'-u)*(1-(c : ℝ)^2)*beta W G c := by positivity
  have hmul := mul_le_mul_of_nonneg_left (hda.trans (le_add_of_nonneg_right hdb)) hgap
  rw [dual_factor W u' hG,dual_factor W u hG]
  unfold g
  nlinarith [hmul]

end polyak.Boundary
