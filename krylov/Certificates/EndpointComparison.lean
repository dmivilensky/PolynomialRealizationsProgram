import krylov.LotkaVolterra.GlobalEndpointUniqueness
import krylov.LotkaVolterra.GlobalExpandingLimit

/-!
Article: main_krylov, apC:prop:digits, endpoint certificate comparison.
A bounded separating graph is trapped by bounded rational sub/supersolutions.
The expanding scalar field rules out a persistent positive difference; the
proof reuses the established bounded-growth contradiction, without a numerical
trajectory or an assumed error estimate. Source: scalar differential comparison.
-/
namespace krylov.Certificates
noncomputable section
open Set
open krylov.LotkaVolterra

/-- The endpoint field expands throughout the slightly enlarged barrier strip. -/
theorem endpoint_field_expansion {U e f : ℝ} (hU : 1 ≤ U)
    (he : e ∈ Icc (1 : ℝ) 4) (hf : f ∈ Icc (1 : ℝ) 4) (hfe : f < e) :
    (e - f) / 7 ≤ endpointGraphRate U e - endpointGraphRate U f := by
  have hd : 0 < (e + 1) * (f + 1) := mul_pos (by linarith [he.1]) (by linarith [hf.1])
  have hdlo : 4 ≤ (e + 1) * (f + 1) := by
    nlinarith [he.1, hf.1, mul_nonneg (show 0 ≤ e - 1 by linarith [he.1])
      (show 0 ≤ f - 1 by linarith [hf.1])]
  have hdhi : (e + 1) * (f + 1) ≤ 25 := by
    calc
      (e + 1) * (f + 1) ≤ 5 * (f + 1) := mul_le_mul_of_nonneg_right
        (by linarith [he.2]) (by linarith [hf.1])
      _ ≤ 25 := by linarith [hf.2]
  have hq : 1 / 7 ≤ 4 / ((e + 1) * (f + 1)) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  have hq' : 4 / ((e + 1) * (f + 1)) ≤ 1 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hb : 0 ≤ (2 - 4 / ((e + 1) * (f + 1))) / U :=
    div_nonneg (by linarith) (by linarith)
  rw [endpointGraphRate_sub (by linarith) (by linarith [he.1]) (by linarith [hf.1])]
  nlinarith [mul_nonneg (show 0 ≤ e - f by linarith) (show 0 ≤
    4 / ((e + 1) * (f + 1)) + (2 - 4 / ((e + 1) * (f + 1))) / U - 1 / 7 by linarith)]

/-- A bounded supersolution of the expanding endpoint equation lies below
its unique bounded solution: comparison runs backward from infinity. -/
theorem endpoint_lower_barrier {e b b' : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U)
    (hb : ∀ U ≥ 1, b U ∈ Icc (1 : ℝ) 4 ∧ HasDerivAt b (b' U) U ∧
      endpointGraphRate U (b U) ≤ b' U) : ∀ U ≥ 1, b U ≤ e U := by
  intro U hU
  have hh : b U - e U ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have h := bounded_solution_le_of_positive_rate (T := 1) (a := ε) (B := 3)
      (v := fun V ↦ b V - e V)
      (v' := fun V ↦ b' V - endpointGraphRate V (e V))
      (show 0 < ε / 7 by positivity)
      (fun V hV ↦ (hb V hV).2.1.sub (he V hV).2)
      (fun V hV ↦ by linarith [(hb V hV).1.2, (he V hV).1.1])
      (fun V hV hd ↦ ?_) U hU
    · simpa only [zero_add] using h
    · have hc := endpoint_field_expansion hV (hb V hV).1
        ⟨(he V hV).1.1, (he V hV).1.2.trans (by norm_num)⟩
        (show e V < b V by linarith)
      linarith [(hb V hV).2.2]
  linarith

/-- A bounded subsolution of the expanding endpoint equation lies above
its bounded physical solution. -/
theorem endpoint_upper_barrier {e b b' : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧ HasDerivAt e (endpointGraphRate U (e U)) U)
    (hb : ∀ U ≥ 1, b U ∈ Icc (1 : ℝ) 4 ∧ HasDerivAt b (b' U) U ∧
      b' U ≤ endpointGraphRate U (b U)) : ∀ U ≥ 1, e U ≤ b U := by
  intro U hU
  have hh : e U - b U ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    have h := bounded_solution_le_of_positive_rate (T := 1) (a := ε) (B := 2)
      (v := fun V ↦ e V - b V)
      (v' := fun V ↦ endpointGraphRate V (e V) - b' V)
      (show 0 < ε / 7 by positivity)
      (fun V hV ↦ (he V hV).2.sub (hb V hV).2.1)
      (fun V hV ↦ by linarith [(he V hV).1.2, (hb V hV).1.1])
      (fun V hV hd ↦ ?_) U hU
    · simpa only [zero_add] using h
    · have hc := endpoint_field_expansion hV
        ⟨(he V hV).1.1, (he V hV).1.2.trans (by norm_num)⟩ (hb V hV).1
        (show b V < e V by linarith)
      linarith [(hb V hV).2.2]
  linarith

end
end krylov.Certificates
