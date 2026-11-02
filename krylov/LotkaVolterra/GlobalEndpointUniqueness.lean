import krylov.LotkaVolterra.GlobalEndpointGraph
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: `main_krylov`, uniqueness of the endpoint separating graph.

An elementary expansion estimate replaces a value-function uniqueness
argument: on `U ≥ 1`, `1 ≤ e ≤ 3`, the scalar graph field has state slope at
least `1/4`. The squared distance between two different solutions would
therefore grow without bound, contradicting the strip bound.

Source: the scalar mean-value argument for expanding ODEs. All constants
are checked directly for the actual endpoint graph field.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set

/-- Exact secant slope of the scalar graph field. -/
theorem endpointGraphRate_sub {U e f : ℝ} (hU : U ≠ 0)
    (he : e + 1 ≠ 0) (hf : f + 1 ≠ 0) :
    endpointGraphRate U e - endpointGraphRate U f =
      (e - f) * (4 / ((e + 1) * (f + 1)) +
        (2 - 4 / ((e + 1) * (f + 1))) / U) := by
  unfold endpointGraphRate
  field_simp
  ring

/-- Quantitative expansion on the full closed physical strip. -/
theorem endpointGraphRate_strongMonotonicity {U e f : ℝ} (hU : 1 ≤ U)
    (he : e ∈ Icc (1 : ℝ) 3) (hf : f ∈ Icc (1 : ℝ) 3) :
    (e - f) ^ 2 / 4 ≤ (e - f) * (endpointGraphRate U e - endpointGraphRate U f) := by
  have hep : 0 < e + 1 := by linarith [he.1]
  have hfp : 0 < f + 1 := by linarith [hf.1]
  have hden := mul_pos hep hfp
  have hdlo : 4 ≤ (e + 1) * (f + 1) := by
    nlinarith [he.1, hf.1, mul_nonneg (show 0 ≤ e - 1 by linarith [he.1])
      (show 0 ≤ f - 1 by linarith [hf.1])]
  have hdhi : (e + 1) * (f + 1) ≤ 16 := by
    calc
      (e + 1) * (f + 1) ≤ 4 * (f + 1) := mul_le_mul_of_nonneg_right
        (by linarith [he.2]) hfp.le
      _ ≤ 16 := by linarith [hf.2]
  have hq : 1 / 4 ≤ 4 / ((e + 1) * (f + 1)) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  have hq' : 4 / ((e + 1) * (f + 1)) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hb : 0 ≤ (2 - 4 / ((e + 1) * (f + 1))) / U :=
    div_nonneg (by linarith) (by linarith)
  rw [endpointGraphRate_sub (ne_of_gt (by linarith : 0 < U)) (ne_of_gt hep) (ne_of_gt hfp)]
  nlinarith [mul_nonneg (sq_nonneg (e - f)) (show 0 ≤
    4 / ((e + 1) * (f + 1)) + (2 - 4 / ((e + 1) * (f + 1))) / U - 1 / 4 by linarith)]

/-- Two actual global endpoint graph solutions in the strip coincide.
This conclusion is obtained directly from the ODE, independently of the
continuum value-function comparison. -/
theorem endpoint_graph_gap_unique {e f : ℝ → ℝ}
    (he : ∀ U ≥ 1, e U ∈ Icc (1 : ℝ) 3 ∧
      HasDerivAt e (endpointGraphRate U (e U)) U)
    (hf : ∀ U ≥ 1, f U ∈ Icc (1 : ℝ) 3 ∧
      HasDerivAt f (endpointGraphRate U (f U)) U) : EqOn e f (Ici 1) := by
  let D : ℝ → ℝ := fun U ↦ (e U - f U) ^ 2
  have hd (U : ℝ) (hU : 1 ≤ U) : HasDerivAt D
      (2 * (e U - f U) * (endpointGraphRate U (e U) - endpointGraphRate U (f U))) U := by
    convert ((he U hU).2.sub (hf U hU).2).pow 2 using 1
    simp only [Pi.sub_apply, show (2 - 1 : ℕ) = 1 by decide, pow_one, Nat.cast_ofNat]
  have hDgrow (U : ℝ) (hU : 1 ≤ U) : D U / 2 ≤ deriv D U := by
    rw [(hd U hU).deriv]
    have hh := endpointGraphRate_strongMonotonicity hU (he U hU).1 (hf U hU).1
    dsimp [D]
    linarith
  have hmono : MonotoneOn D (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (HasDerivAt.continuousOn fun U hU ↦ hd U hU)
    · intro U hU
      exact (hd U (interior_subset hU)).differentiableAt.differentiableWithinAt
    · intro U hU
      have hu : 1 ≤ U := interior_subset hU
      exact (div_nonneg (sq_nonneg _) (by norm_num)).trans (hDgrow U hu)
  intro U hU
  by_contra hne
  have hpos : 0 < D U := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  let V : ℝ := U + 10 / D U
  have hUV : U < V := by dsimp [V]; exact lt_add_of_pos_right U (div_pos (by norm_num) hpos)
  have hV : 1 ≤ V := hU.trans hUV.le
  have hgrow : D U / 2 * (V - U) ≤ D V - D U := by
    apply (convex_Ici U).mul_sub_le_image_sub_of_le_deriv
      (HasDerivAt.continuousOn fun t ht ↦ hd t (hU.trans ht))
      (fun t ht ↦ (hd t (hU.trans (interior_subset ht))).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ (div_le_div_of_nonneg_right (hmono hU (hU.trans (interior_subset ht))
        (interior_subset ht)) (by norm_num)).trans (hDgrow t (hU.trans (interior_subset ht))))
      U (mem_Ici.mpr le_rfl) V (mem_Ici.mpr hUV.le) hUV.le
  have hb : D V ≤ 4 := by
    have heV := (he V hV).1
    have hfV := (hf V hV).1
    dsimp [D]
    nlinarith [sq_nonneg (e V - f V - 2), sq_nonneg (e V - f V + 2),
      mul_nonneg (show 0 ≤ e V - f V + 2 by linarith [heV.1, hfV.2])
        (show 0 ≤ 2 - (e V - f V) by linarith [heV.2, hfV.1])]
  have hid : D U / 2 * (V - U) = 5 := by dsimp [V]; field_simp; ring
  rw [hid] at hgrow
  linarith

end
end krylov.LotkaVolterra
