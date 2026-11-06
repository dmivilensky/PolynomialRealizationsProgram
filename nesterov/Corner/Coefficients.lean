import nesterov.TwoStep.ScaledCoefficientsUniform

/-! Exact member-parameter corner expansions, with compact-uniform O(epsilon^2) remainders. -/
namespace nesterov.Corner
noncomputable section
open Set
open TwoStep

abbrev Parameters := Fin 4→ℝ

def physicalParameters (ε : ℝ) (p : Parameters) : ScaledParameters :=
  ![p 0,p 1,2-p 3*ε,1/2-p 2*ε]

def first (p : Parameters) : Fin 6→ℝ :=
  ![4*(p 1-3*p 0),2*(p 1+2*p 0-4*p 2),2*(4*p 2+p 3-2*p 1),
    4*(p 1-2*p 0),2*(p 1+p 0-4*p 2),2*(4*p 2+p 3-2*p 1)]

def correction (ε : ℝ) (p : Parameters) : Fin 6→ℝ :=
  ![p 3*(6*p 0-2*p 1),
    4*p 2*p 3+p 2*(32*p 0-4*p 1)-p 1*p 3+ε*p 2*p 3*(2*p 1-16*p 0),
    -4*p 2*p 3-24*p 0*p 2-6*p 0*p 3+12*p 0*p 2*p 3*ε,
    p 3*(4*p 0-2*p 1),
    4*p 2*p 3+p 2*(20*p 0-4*p 1)-p 3*(p 0+p 1)+ε*p 2*p 3*(2*p 1-10*p 0),
    -4*p 2*p 3-16*p 0*p 2-4*p 0*p 3+8*p 0*p 2*p 3*ε]

def remainder (ε : ℝ) (p : Parameters) (k : Fin 6) : ℝ :=
  correction ε p k+coefficientRemainder ε (physicalParameters ε p) k

theorem coefficient_exact (ε : ℝ) (p : Parameters) (k : Fin 6) :
    scaledCoefficient ε (physicalParameters ε p) k=ε*first p k+ε^2*remainder ε p k := by
  rw [scaled_coefficient_exact]
  fin_cases k <;>
    simp only [zeroCoefficient,firstCoefficient,physicalParameters,first,remainder,correction,
      dotP1,dotP2,dotP3,dotQ0,dotQ1,dotQ2] <;> norm_num <;> ring

theorem continuous_remainder (k : Fin 6) :
    Continuous (fun x : ℝ×Parameters=>remainder x.1 x.2 k) := by
  have hp : Continuous (fun x : ℝ×Parameters=>(x.1,physicalParameters x.1 x.2)) := by
    apply Continuous.prodMk continuous_fst
    apply continuous_pi
    intro j
    fin_cases j <;> dsimp [physicalParameters] <;> fun_prop
  apply Continuous.add _ ((continuous_coefficientRemainder k).comp hp)
  fin_cases k <;> dsimp [correction] <;> fun_prop

theorem uniform_second_order (k : Fin 6) {K : Set Parameters} (hK : IsCompact K) :
    ∃ M : ℝ,0≤M ∧ ∀ ε : ℝ,|ε|≤1 → ∀ p∈K,
      |scaledCoefficient ε (physicalParameters ε p) k-ε*first p k|≤M*ε^2 := by
  obtain ⟨M,hM⟩ := ((isCompact_Icc.prod hK).image (continuous_remainder k)).isBounded.exists_norm_le
  refine ⟨|M|,abs_nonneg M,fun ε hε p hp=>?_⟩
  have hh := hM (remainder ε p k) ⟨(ε,p),⟨abs_le.mp hε,hp⟩,rfl⟩
  have hh' : |remainder ε p k|≤|M| := (show |remainder ε p k|≤M by simpa only [Real.norm_eq_abs] using hh).trans (le_abs_self M)
  rw [coefficient_exact,add_sub_cancel_left,abs_mul,abs_of_nonneg (sq_nonneg ε)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh' (sq_nonneg ε)

end
end nesterov.Corner
