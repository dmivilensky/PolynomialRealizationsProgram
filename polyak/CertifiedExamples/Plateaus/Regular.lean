import polyak.CertifiedExamples.Plateaus.Assembly
import polyak.CertifiedExamples.Plateaus.SourcePrimal
import polyak.CertifiedExamples.Plateaus.DualJets
import polyak.CertifiedExamples.Plateaus.PinningBounds
import polyak.CertifiedExamples.Plateaus.SymbolResults

/-! Unconditional source-level regular certificates at the two selected scalar
boundary roots. No numerical certificate record is assumed as a hypothesis. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels ModeLocking
open polyak.Certificates.PartII.Plateaus
open scoped BigOperators

theorem sourceLagMatrix18_eq : sourceLagMatrix tuning18 first18 atoms18=sourceMatrix18 := by
  ext r i
  exact (sourceMatrix18_actual r i).symm

theorem sourceLagMatrix21_eq : sourceLagMatrix tuning21 first21 atoms21=sourceMatrix21 := by
  ext r i
  exact (sourceMatrix21_actual r i).symm

def primary18 : PolynomialPrimaryData tuning18 18 2 where
  period_ge := by norm_num
  dimension_pos := by norm_num
  atoms := atoms18
  atoms_injective := gridAtom_injective 18 (by norm_num)
  atoms_grid := gridAtom_grid 18 (by norm_num)
  atoms_lt_pi := fun i=>(gridAtom_interior 18 (by norm_num) i).2
  reps := reps18
  reps_pos := row18_reps_pos
  reps_lt := row18_reps_lt
  reps_injective := row18_reps_injective
  baseLag := first18
  base_nonzero := row18_first_nonzero
  base_mod := row18_first_mod
  rho := rho18
  rho_pos := rho18_positive
  kernel := by
    intro r
    simp only [sourceLagMatrix18_eq]
    simpa only [sourceMatrix18_actual] using rho18_kernel r
  inactive := inactive18
  minimizer := minimizer18
  rank := by rw [sourceLagMatrix18_eq]; exact rank18
  lags := lags18
  lags_nonzero := row18_lags_nonzero
  classes := row18_classes
  dual := dual18
  dual_pos := row18_dual_pos weights18_positive
  dual_sum := row18_dual_sum row18_mu_sum
  lag_one := row18_lag_one
  class_pair := row18_class_pair
  pinning_det := row18_actual_pinning_det

def primary21 : PolynomialPrimaryData tuning21 21 3 where
  period_ge := by norm_num
  dimension_pos := by norm_num
  atoms := atoms21
  atoms_injective := gridAtom_injective 21 (by norm_num)
  atoms_grid := gridAtom_grid 21 (by norm_num)
  atoms_lt_pi := fun i=>(gridAtom_interior 21 (by norm_num) i).2
  reps := reps21
  reps_pos := row21_reps_pos
  reps_lt := row21_reps_lt
  reps_injective := row21_reps_injective
  baseLag := first21
  base_nonzero := row21_first_nonzero
  base_mod := row21_first_mod
  rho := rho21
  rho_pos := rho21_positive
  kernel := by
    intro r
    simp only [sourceLagMatrix21_eq]
    simpa only [sourceMatrix21_actual] using rho21_kernel r
  inactive := inactive21
  minimizer := minimizer21
  rank := by rw [sourceLagMatrix21_eq]; exact rank21
  lags := lags21
  lags_nonzero := row21_lags_nonzero
  classes := row21_classes
  dual := dual21
  dual_pos := row21_dual_pos weights21_positive
  dual_sum := row21_dual_sum row21_mu_sum
  lag_one := row21_lag_one
  class_pair := row21_class_pair
  pinning_det := row21_actual_pinning_det

theorem row18_polynomial_curvature_actual (i : Fin 2) :
    deriv^[2] (polynomialSymbol tuning18 lags18 dual18) (coordinates18 i)<0 := by
  rw [polynomial18_eq_indexed]
  exact row18_polynomial_curvature tuning18 weights18 coordinates18
    tuning18_Xi_mem weights18_mem coordinates18_mem i

theorem row21_polynomial_curvature_actual (i : Fin 3) :
    deriv^[2] (polynomialSymbol tuning21 lags21 dual21) (coordinates21 i)<0 := by
  rw [polynomial21_eq_indexed]
  exact row21_polynomial_curvature tuning21 weights21 coordinates21
    tuning21_Xi_mem weights21_mem coordinates21_mem i

theorem row18_polynomial_strict_actual {c : ℝ} (hc : c∈Set.Icc (-1:ℝ) 1)
    (hne : ∀i,c≠coordinates18 i) : polynomialSymbol tuning18 lags18 dual18 c<0 := by
  rw [polynomial18_eq_indexed]
  apply row18_global_polynomial tuning18 weights18 coordinates18
    tuning18_Xi_mem weights18_mem coordinates18_mem
  · simpa only [←polynomial18_eq_indexed] using row18_polynomial_zero
  · simpa only [←polynomial18_eq_indexed] using row18_polynomial_slope
  · exact hc
  · exact hne

theorem row21_polynomial_strict_actual {c : ℝ} (hc : c∈Set.Icc (-1:ℝ) 1)
    (hne : ∀i,c≠coordinates21 i) : polynomialSymbol tuning21 lags21 dual21 c<0 := by
  rw [polynomial21_eq_indexed]
  apply row21_global_polynomial tuning21 weights21 coordinates21
    tuning21_Xi_mem weights21_mem coordinates21_mem
  · simpa only [←polynomial21_eq_indexed] using row21_polynomial_zero
  · simpa only [←polynomial21_eq_indexed] using row21_polynomial_slope
  · exact hc
  · exact hne

def row18_regularData : RegularData tuning18 0 18 := primary18.regularData
  row18_polynomial_zero row18_polynomial_slope row18_polynomial_curvature_actual
  (fun _ hc hne=>row18_polynomial_strict_actual hc hne)

def row21_regularData : RegularData tuning21 0 21 := primary21.regularData
  row21_polynomial_zero row21_polynomial_slope row21_polynomial_curvature_actual
  (fun _ hc hne=>row21_polynomial_strict_actual hc hne)

theorem row18_gap : Geometry.Gap 4 tuning18 :=
  row18_in_gap_four tuning18 rfl rfl tuning18_kappa_mem

theorem row21_gap : Geometry.Gap 4 tuning21 :=
  row21_in_gap_four tuning21 rfl rfl tuning21_kappa_mem

end polyak.CertifiedExamples.Plateaus
