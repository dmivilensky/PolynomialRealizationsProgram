import polyak.CertifiedExamples.Plateaus.DualStatic
import polyak.CertifiedExamples.Plateaus.DualBounds
import polyak.CertifiedExamples.Plateaus.Primal

/-! Exact normalization and support jets of the two actual lifted duals.
The equalities follow from the genuine determinant roots and Cramer solves. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels ModeLocking
open polyak.Certificates.PartII.Plateaus
open scoped BigOperators

theorem mu18_positive (i:Fin 2) : 0<mu18 i := by
  have hp:(0:ℝ)<(row18Left i).lo := by exact_mod_cast row18_left_positive i
  exact hp.trans_le (mu18_mem i).1

theorem mu21_positive (i:Fin 3) : 0<mu21 i := by
  have hp:(0:ℝ)<(row21Left i).lo := by exact_mod_cast row21_left_positive i
  exact hp.trans_le (mu21_mem i).1

theorem row18_mu_sum : (∑i,mu18 i)=1 := by
  apply normalizeVector_sum
  intro hz
  have h:=mu18_positive 0
  simp only [mu18,positiveDual,normalizeVector,hz,div_zero] at h
  exact lt_irrefl 0 h

theorem row21_mu_sum : (∑i,mu21 i)=1 := by
  apply normalizeVector_sum
  intro hz
  have h:=mu21_positive 0
  simp only [mu21,positiveDual,normalizeVector,hz,div_zero] at h
  exact lt_irrefl 0 h

theorem coordinateLag_grid_eq {L:ℕ} (q:Tuning) (ω:Frequency)
    (hω:0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi) (hg:ω∈periodicGrid L)
    (n m:ℤ) (hn:n≠0) (hm:m≠0) (he:n%(L:ℤ)=m%(L:ℤ)) :
    coordinateLag (coefficientVector q) n (Real.cos (ω:ℝ))=
      coordinateLag (coefficientVector q) m (Real.cos (ω:ℝ)) := by
  apply mul_left_cancel₀ (phaseFactor_pos q ω hω).ne'
  simp only [phaseFactor,coordinateLag_actual_vector]
  rw [←Farey.Certificates.lag_polynomial_factor q n hn ω hω,
    ←Farey.Certificates.lag_polynomial_factor q m hm ω hω,
    lag_mod_grid _ hg n,lag_mod_grid _ hg m,he]

private theorem coordinate_ne_one {ω:Frequency} (hω:0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi) :
    Real.cos (ω:ℝ)≠1 := by
  have h:=Real.strictAntiOn_cos
    (show (0:ℝ)∈Set.Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩) ω.property hω.1
  exact (show Real.cos (ω:ℝ)<1 by simpa only [Real.cos_zero] using h).ne

private theorem jets18 (i:Fin 2) :
    pairPolynomial tuning18 first18 lifts18 mu18 moments18 (coordinates18 i)=0 ∧
      deriv (pairPolynomial tuning18 first18 lifts18 mu18 moments18) (coordinates18 i)=0 := by
  apply pair_polynomial_double_zero tuning18 first18 lifts18 coordinates18 mu18
  · intro j
    exact positiveDual_kernel sourceMatrix18 0 sourceMatrix18_det_zero j
  · intro j r
    apply coordinateLag_grid_eq tuning18 (atoms18 j)
      (gridAtom_interior 18 (by norm_num) j) (gridAtom_grid 18 (by norm_num) j)
      (lifts18 r) (first18 r)
    · fin_cases r <;> decide
    · exact row18_first_nonzero r
    · exact (row18_lifts_mod r).trans (row18_first_mod r).symm
  · exact slope18_det_ne
  · intro j
    exact coordinate_ne_one (gridAtom_interior 18 (by norm_num) j)

private theorem jets21 (i:Fin 3) :
    pairPolynomial tuning21 first21 lifts21 mu21 moments21 (coordinates21 i)=0 ∧
      deriv (pairPolynomial tuning21 first21 lifts21 mu21 moments21) (coordinates21 i)=0 := by
  apply pair_polynomial_double_zero tuning21 first21 lifts21 coordinates21 mu21
  · intro j
    exact positiveDual_kernel sourceMatrix21 0 sourceMatrix21_det_zero j
  · intro j r
    apply coordinateLag_grid_eq tuning21 (atoms21 j)
      (gridAtom_interior 21 (by norm_num) j) (gridAtom_grid 21 (by norm_num) j)
      (lifts21 r) (first21 r)
    · fin_cases r <;> decide
    · exact row21_first_nonzero r
    · exact (row21_lifts_mod r).trans (row21_first_mod r).symm
  · exact slope21_det_ne
  · intro j
    exact coordinate_ne_one (gridAtom_interior 21 (by norm_num) j)

theorem row18_polynomial_zero (i:Fin 2) :
    polynomialSymbol tuning18 lags18 dual18 (coordinates18 i)=0 := by
  rw [polynomial18_eq_pair]
  exact (jets18 i).1

theorem row21_polynomial_zero (i:Fin 3) :
    polynomialSymbol tuning21 lags21 dual21 (coordinates21 i)=0 := by
  rw [polynomial21_eq_pair]
  exact (jets21 i).1

theorem row18_polynomial_slope (i:Fin 2) :
    deriv (polynomialSymbol tuning18 lags18 dual18) (coordinates18 i)=0 := by
  rw [polynomial18_eq_pair]
  exact (jets18 i).2

theorem row21_polynomial_slope (i:Fin 3) :
    deriv (polynomialSymbol tuning21 lags21 dual21) (coordinates21 i)=0 := by
  rw [polynomial21_eq_pair]
  exact (jets21 i).2

end polyak.CertifiedExamples.Plateaus
