import krylov.Certificates.EndpointRationalField

/-!
Article: main_krylov, apC:prop:digits, certified endpoint crossing.
The bounds hold for every actual globally bounded separating gap, and hence
for the same graph used in the continuum optimizer and discrete sharp limit.
The rational differential barriers prove the numerical enclosure directly;
there is no premise asserting a successful external numerical computation.
Source: the exact rational witnesses and bounded expanding comparison.
-/
namespace krylov.Certificates
noncomputable section
open Set
open krylov.LotkaVolterra

/-- Kernel-certified enclosure of the genuine endpoint separating value. -/
theorem endpoint_certified_crossing_bounds {e : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) :
    (264667 / 100000 : ℝ) < 1 + e 1 ∧ 1 + e 1 < (264668 / 100000 : ℝ) := by
  have hlo := endpoint_lower_barrier he (fun U hU ↦ endpointRational_lower_field U hU) 1 le_rfl
  have hhi := endpoint_upper_barrier he (fun U hU ↦ endpointRational_upper_field U hU) 1 le_rfl
  have hlo' : (264667 / 100000 : ℝ) < 1 + endpointRationalBarrier (-(1 / 500000)) 1 := by
    norm_num [endpointRationalBarrier, endpointNumerator, endpointDenominator]
  have hhi' : 1 + endpointRationalBarrier (1 / 500000) 1 < (264668 / 100000 : ℝ) := by
    norm_num [endpointRationalBarrier, endpointNumerator, endpointDenominator]
  constructor <;> linarith

/-- The endpoint numerical enclosure has an actual graph witness supplied
by the existing unconditional global shooting construction. -/
theorem exists_certified_endpoint_graph :
    ∃ e : ℝ → ℝ,
      (∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U) ∧
      (264667 / 100000 : ℝ) < 1 + e 1 ∧ 1 + e 1 < (264668 / 100000 : ℝ) := by
  obtain ⟨e, he⟩ := exists_global_endpoint_graph_gap
  exact ⟨e, he, endpoint_certified_crossing_bounds he⟩

end
end krylov.Certificates
