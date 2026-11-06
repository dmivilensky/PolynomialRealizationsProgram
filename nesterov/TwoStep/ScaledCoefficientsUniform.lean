import nesterov.TwoStep.ScaledCoefficients
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-! Uniformity of every coefficient remainder on arbitrary compact sets of
all four independent parameters, including the test exponent c. -/
namespace nesterov.TwoStep
noncomputable section
open Set

abbrev ScaledParameters := Fin 4→ℝ

def scaledCoefficient (ε : ℝ) (p : ScaledParameters) : Fin 6→ℝ :=
  ![scaledP1 ε (p 0) (p 1) (p 2) (p 3),scaledP2 ε (p 0) (p 1) (p 2) (p 3),
    scaledP3 ε (p 0) (p 1) (p 2) (p 3),scaledQ0 ε (p 0) (p 1) (p 2) (p 3),
    scaledQ1 ε (p 0) (p 1) (p 2) (p 3),scaledQ2 ε (p 0) (p 1) (p 2) (p 3)]
def zeroCoefficient (p : ScaledParameters) : Fin 6→ℝ :=
  ![0,2*p 2*(2*p 3-1),4*(1-p 3*p 2),0,2*p 2*(2*p 3-1),4*(1-p 3*p 2)]
def firstCoefficient (p : ScaledParameters) : Fin 6→ℝ :=
  ![dotP1 (p 0) (p 1) (p 2) (p 3),dotP2 (p 0) (p 1) (p 2) (p 3),
    dotP3 (p 0) (p 1) (p 2) (p 3),dotQ0 (p 0) (p 1) (p 2) (p 3),
    dotQ1 (p 0) (p 1) (p 2) (p 3),dotQ2 (p 0) (p 1) (p 2) (p 3)]
def coefficientRemainder (ε : ℝ) (p : ScaledParameters) : Fin 6→ℝ :=
  ![remainderP1 ε (p 0) (p 1) (p 2) (p 3),remainderP2 ε (p 0) (p 1) (p 2) (p 3),
    remainderP3 ε (p 0) (p 1) (p 2) (p 3),remainderQ0 ε (p 0) (p 1) (p 2) (p 3),
    remainderQ1 ε (p 0) (p 1) (p 2) (p 3),remainderQ2 ε (p 0) (p 1) (p 2) (p 3)]

theorem scaled_coefficient_exact (ε : ℝ) (p : ScaledParameters) (k : Fin 6) :
    scaledCoefficient ε p k=zeroCoefficient p k+ε*firstCoefficient p k+
      ε^2*coefficientRemainder ε p k := by
  fin_cases k
  · simpa [scaledCoefficient,zeroCoefficient,firstCoefficient,coefficientRemainder] using scaledP1_exact ε (p 0) (p 1) (p 2) (p 3)
  · exact scaledP2_exact ε (p 0) (p 1) (p 2) (p 3)
  · exact scaledP3_exact ε (p 0) (p 1) (p 2) (p 3)
  · simpa [scaledCoefficient,zeroCoefficient,firstCoefficient,coefficientRemainder] using scaledQ0_exact ε (p 0) (p 1) (p 2) (p 3)
  · exact scaledQ1_exact ε (p 0) (p 1) (p 2) (p 3)
  · exact scaledQ2_exact ε (p 0) (p 1) (p 2) (p 3)

theorem continuous_coefficientRemainder (k : Fin 6) :
    Continuous (fun x : ℝ×ScaledParameters=>coefficientRemainder x.1 x.2 k) := by
  fin_cases k <;> dsimp [coefficientRemainder,remainderP1,remainderP2,remainderP3,remainderQ0,remainderQ1,remainderQ2] <;> fun_prop

theorem continuous_firstCoefficient (k : Fin 6) : Continuous (fun p=>firstCoefficient p k) := by
  fin_cases k <;> dsimp [firstCoefficient,dotP1,dotP2,dotP3,dotQ0,dotQ1,dotQ2] <;> fun_prop

theorem continuous_zeroCoefficient (k : Fin 6) : Continuous (fun p=>zeroCoefficient p k) := by
  fin_cases k <;> dsimp [zeroCoefficient] <;> fun_prop

private theorem compact_parameter_bound {H : ℝ×ScaledParameters→ℝ} (hH : Continuous H)
    {K : Set ScaledParameters} (hK : IsCompact K) :
    ∃ M : ℝ,0≤M ∧ ∀ ε : ℝ,|ε|≤1 → ∀ p∈K,|H (ε,p)|≤M := by
  obtain ⟨M,hM⟩ := ((isCompact_Icc.prod hK).image hH).isBounded.exists_norm_le
  refine ⟨|M|,abs_nonneg M,fun ε hε p hp=>?_⟩
  have hh := hM (H (ε,p)) ⟨(ε,p),⟨abs_le.mp hε,hp⟩,rfl⟩
  have hh' : |H (ε,p)|≤M := by simpa only [Real.norm_eq_abs] using hh
  exact hh'.trans (le_abs_self M)

/-- One uniform O(ε²) bound for each of all six source coefficient remainders. -/
theorem uniform_second_order (k : Fin 6) {K : Set ScaledParameters} (hK : IsCompact K) :
    ∃ M : ℝ,0≤M ∧ ∀ ε : ℝ,|ε|≤1 → ∀ p∈K,
      |scaledCoefficient ε p k-zeroCoefficient p k-ε*firstCoefficient p k|≤M*ε^2 := by
  obtain ⟨M,hM,hbound⟩ := compact_parameter_bound (continuous_coefficientRemainder k) hK
  refine ⟨M,hM,fun ε hε p hp=>?_⟩
  have he : scaledCoefficient ε p k-zeroCoefficient p k-ε*firstCoefficient p k=
      ε^2*coefficientRemainder ε p k := by rw [scaled_coefficient_exact];ring
  rw [he,abs_mul,abs_of_nonneg (sq_nonneg ε)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound ε hε p hp) (sq_nonneg ε)

/-- The zeroth-order versions in parts (a,b) are uniform on the same compact sets. -/
theorem uniform_first_order (k : Fin 6) {K : Set ScaledParameters} (hK : IsCompact K) :
    ∃ M : ℝ,0≤M ∧ ∀ ε : ℝ,|ε|≤1 → ∀ p∈K,
      |scaledCoefficient ε p k-zeroCoefficient p k|≤M*|ε| := by
  have hc : Continuous (fun x : ℝ×ScaledParameters=>
      firstCoefficient x.2 k+x.1*coefficientRemainder x.1 x.2 k) :=
    ((continuous_firstCoefficient k).comp continuous_snd).add
      (continuous_fst.mul (continuous_coefficientRemainder k))
  obtain ⟨M,hM,hbound⟩ := compact_parameter_bound hc hK
  refine ⟨M,hM,fun ε hε p hp=>?_⟩
  have he : scaledCoefficient ε p k-zeroCoefficient p k=
      ε*(firstCoefficient p k+ε*coefficientRemainder ε p k) := by
    rw [scaled_coefficient_exact]
    ring
  rw [he,abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound ε hε p hp) (abs_nonneg ε)

end
end nesterov.TwoStep
