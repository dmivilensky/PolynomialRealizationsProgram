import nesterov.Corner.Coefficients
import nesterov.TwoStep.Alternating

/-! Literal endpoint expansions with the member damping coefficient retained. -/
namespace nesterov.Corner
noncomputable section
open Set TwoStep

def slowRemainder (ε : ℝ) (p : Parameters) : ℝ :=
  -p 3-(2-p 3*ε)*(3/2-p 2*ε)*p 0

def fastRemainder (ε : ℝ) (p : Parameters) : ℝ :=
  slowRemainder ε p+ε*(p 0^2-p 1*p 0)

theorem slow_endpoint_exact (ε : ℝ) (p : Parameters) :
    realCharacteristic (1-p 1*ε) (1/2-p 2*ε) (2-p 3*ε) (ε^2) (1-p 0*ε)=
      ε^2*(p 0^2-p 1*p 0+2+ε*slowRemainder ε p) := by
  unfold realCharacteristic Quadratic.S Quadratic.Q slowRemainder
  ring

theorem fast_endpoint_exact (ε : ℝ) (p : Parameters) :
    realCharacteristic (1-p 1*ε) (1/2-p 2*ε) (2-p 3*ε) 1 (1-p 0*ε)=
      2+ε*fastRemainder ε p := by
  unfold realCharacteristic Quadratic.S Quadratic.Q fastRemainder slowRemainder
  ring

theorem largest_gap_exact (ε θ a b : ℝ) :
    realCharacteristic (1-θ*ε) (1/2-a*ε) (2-b*ε) 1 (-1)=
      (4*a+2*b-2*θ)*ε-2*a*b*ε^2 := by
  unfold realCharacteristic Quadratic.S Quadratic.Q
  ring

theorem largest_S_exact (ε θ a b : ℝ) :
    Quadratic.S (1-θ*ε) (1/2-a*ε) (2-b*ε) 1=
      -1+ε*(2*a+3*b/2-θ-a*b*ε) := by
  unfold Quadratic.S
  ring

theorem uniform_endpoint_remainder (k : Fin 2) {K : Set Parameters} (hK : IsCompact K) :
    ∃ M : ℝ,0≤M ∧ ∀ ε : ℝ,|ε|≤1 → ∀ p∈K,
      |(![slowRemainder ε p,fastRemainder ε p] : Fin 2→ℝ) k|≤M := by
  have hc : Continuous (fun x : ℝ×Parameters=>(![slowRemainder x.1 x.2,fastRemainder x.1 x.2] : Fin 2→ℝ) k) := by
    fin_cases k <;> dsimp [slowRemainder,fastRemainder] <;> fun_prop
  obtain ⟨M,hM⟩ := ((isCompact_Icc.prod hK).image hc).isBounded.exists_norm_le
  refine ⟨|M|,abs_nonneg M,fun ε hε p hp=>?_⟩
  have hh := hM _ ⟨(ε,p),⟨abs_le.mp hε,hp⟩,rfl⟩
  exact (show |(![slowRemainder ε p,fastRemainder ε p] : Fin 2→ℝ) k|≤M by
    simpa only [Real.norm_eq_abs] using hh).trans (le_abs_self M)

end
end nesterov.Corner
