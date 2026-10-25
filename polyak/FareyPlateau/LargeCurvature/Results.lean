import polyak.FareyPlateau.LargeCurvature.Certificate
import polyak.FareyPlateau.Ray.Infimum
import polyak.GapEdges.Boundary.Topology

/-! The full large-curvature conclusion, with the literal source cutoff,
actual regularity, and a finite continuous upper roof for a_F. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open General Levels Set

namespace SourceData
variable {q : Tuning} {j k : ℕ} (B : SourceData q j k)

theorem maximum_lt : B.sourceCertificate.maximum < B.a :=
  (B.sourceCertificate.ray_criterion (by have := B.numerator_ge; omega) B.numerator_lt
    B.inverse_product q B.coefficients).mpr
    ⟨fun x hx hp hne=>B.strict ⟨hx,hp⟩ hne,B.curvature,B.endpoint⟩

include B in
theorem boundary {K : ℕ} (hK : 2 ≤ K) (hf : Chart.FractionInWindow K j k)
    (haE : aE K j k B.D < B.a) : q ∈ ModeLocking.BoundaryInGap K := by
  rw [GapEdges.boundaryInGap_eq_zero]
  exact ⟨(source_edgedomain q hK hf B.coefficients).mpr haE,B.sigma_eq_zero⟩

end SourceData

def upperMajorant (K j k : ℕ) (D : ℝ) : ℝ :=
  max (a1 k (Regions.rationalAngle j k) (Chart.rationalHeight j k) |D|) (aE K j k D)

@[fun_prop] theorem continuous_upperMajorant (K j k : ℕ) : Continuous (upperMajorant K j k) := by
  exact ((continuous_a1 _ _ _).comp continuous_abs).max (continuous_aE K j k)

def sourceDataOf (q : Tuning) {j k : ℕ} (hj : 2 ≤ j) (hjk : 2*j < k)
    (b : ℤ) (hb0 : 0 < b) (hbk : b < k) (hb : b*(j:ℤ) ≡ 1 [ZMOD (k:ℤ)])
    {a D M : ℝ} (hM : 0 ≤ M) (hD : |D| ≤ M)
    (he : Chart.coefficients q=edgeCoefficients (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D)
    (ha : a1 k (Regions.rationalAngle j k) (Chart.rationalHeight j k) M<a) : SourceData q j k where
  numerator_ge := hj
  period_ge := by omega
  numerator_lt := hjk
  inverse := b
  inverse_pos := hb0
  inverse_lt := hbk
  inverse_mod := hb
  a := a
  D := D
  M := M
  max_nonneg := hM
  asymmetry_bound := hD
  coefficients := he
  large := ha

theorem largea (q : Tuning) {K j k : ℕ} (hK : 2 ≤ K) (hf : Chart.FractionInWindow K j k)
    (b : ℤ) (hb0 : 0 < b) (hbk : b < k) (hb : b*(j:ℤ) ≡ 1 [ZMOD (k:ℤ)])
    {a D M : ℝ} (hM : 0 ≤ M) (hD : |D| ≤ M)
    (he : Chart.coefficients q=edgeCoefficients (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D)
    (ha : a1 k (Regions.rationalAngle j k) (Chart.rationalHeight j k) M<a) (haE : aE K j k D<a) :
    q∈ModeLocking.BoundaryInGap K ∧ ModeLocking.RegularPoint q 0 k ∧ Threshold.sigma q=0 ∧
      ∃C : Ray.SourceCertificate j k b D,C.maximum<a := by
  let B := sourceDataOf q (Chart.fraction_window_arithmetic hK hf).1
    (Chart.fraction_window_arithmetic hK hf).2 b hb0 hbk hb hM hD he ha
  exact ⟨B.boundary hK hf haE,B.regular,B.sigma_eq_zero,B.sourceCertificate,B.maximum_lt⟩

theorem sourceCertificate_nonempty {K j k : ℕ} (hK : 2 ≤ K) (hf : Chart.FractionInWindow K j k)
    (b : ℤ) (hb0 : 0 < b) (hbk : b < k) (hb : b*(j:ℤ) ≡ 1 [ZMOD (k:ℤ)]) (D : ℝ) :
    Nonempty (Ray.SourceCertificate j k b D) := by
  let a := upperMajorant K j k D+1
  have haE : aE K j k D<a := lt_add_of_le_of_pos (le_max_right _ _) (by norm_num)
  obtain ⟨q,he,_⟩ := source_edge_exists_unique hK hf haE
  let B := sourceDataOf q (Chart.fraction_window_arithmetic hK hf).1
    (Chart.fraction_window_arithmetic hK hf).2 b hb0 hbk hb (abs_nonneg D) le_rfl he
    (lt_add_of_le_of_pos (le_max_left _ _) (by norm_num))
  exact ⟨B.sourceCertificate⟩

theorem aF_le_upperMajorant {K j k : ℕ} (hK : 2 ≤ K) (hf : Chart.FractionInWindow K j k)
    (b : ℤ) (hb0 : 0 < b) (hbk : b < k) (hb : b*(j:ℤ) ≡ 1 [ZMOD (k:ℤ)]) (D : ℝ) :
    Ray.aF j k b D ≤ upperMajorant K j k D := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro a ha
  have haE : aE K j k D<a := (le_max_right _ _).trans_lt ha
  obtain ⟨q,he,_⟩ := source_edge_exists_unique hK hf haE
  let B := sourceDataOf q (Chart.fraction_window_arithmetic hK hf).1
    (Chart.fraction_window_arithmetic hK hf).2 b hb0 hbk hb (abs_nonneg D) le_rfl he
    ((le_max_left _ _).trans_lt ha)
  exact (Ray.aF_le_maximum B.sourceCertificate (by have := B.numerator_ge; omega)
    B.numerator_lt B.inverse_product).trans B.maximum_lt.le

end polyak.FareyPlateau.LargeCurvature
