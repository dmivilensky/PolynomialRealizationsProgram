import polyak.FareyPlateau.LargeCurvature.SourceData

noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open General Levels Set
open scoped BigOperators
namespace SourceData
variable {q : Tuning} {j k : ℕ} (B : SourceData q j k)

def window : Set ℝ := Icc (B.ω-zoneRadius k B.N) (B.ω+zoneRadius k B.N)

theorem window_trimmed {x : ℝ} (hx : x ∈ B.window) :
    x ∈ Icc (Real.pi/(2*k)) (Real.pi-Real.pi/(2*k)) :=
  central_interval_trimmed B.kr B.N_ge B.ω_lower B.ω_upper hx

theorem far_profile {x : ℝ} (hx : x ∈ Icc (0:ℝ) Real.pi) (hfar : x ∉ B.window) :
    q.Xi (Real.cos x) ≤ -(B.a*B.ε^2)/2 := by
  have hd := zoneRadius_bounds B.kr B.N_ge
  have hl := B.window_trimmed (left_mem_Icc.mpr (by linarith [hd.1] : B.ω-zoneRadius k B.N ≤ B.ω+zoneRadius k B.N))
  have hr := B.window_trimmed (right_mem_Icc.mpr (by linarith [hd.1] : B.ω-zoneRadius k B.N ≤ B.ω+zoneRadius k B.N))
  apply profile_far_upper q B.coefficients (Real.abs_cos_le_one B.ω) (Real.abs_cos_le_one x)
    B.max_nonneg B.asymmetry_bound B.a_pos.le B.epsilon_pos.le
    (cosine_distance_far hd.1 (by
      have hp : 0 < Real.pi/(2*k) := div_pos Real.pi_pos (mul_pos (by norm_num) B.kp)
      linarith [hl.1])
      (by
        have hp : 0 < Real.pi/(2*k) := div_pos Real.pi_pos (mul_pos (by norm_num) B.kp)
        linarith [hr.2]) hx hfar) B.margins.1

theorem far_symbol {x : ℝ} (hx : 0 < x ∧ x ≤ Real.pi) (hfar : x ∉ B.window) :
    indexedSymbol q 0 B.n B.w x < 0 := by
  have hX := B.far_profile ⟨hx.1.le,hx.2⟩ hfar
  have hA : 48*B.N^2 < B.a*B.ε^2 := B.margins.2
  have hw (i) := (B.positive i).le
  rcases eq_or_lt_of_le hx.2 with rfl|hpi
  · rw [indexedSymbol_at_pi]
    have hp := large_angle_denominator (n := B.n₀) (k := (k:ℤ)) (by exact_mod_cast B.period_ge) B.N_ge
      (by simpa [n,integerLag] using B.lag_abs (1:Fin 3)) B.coprime B.w
      (fun i=>(weight_bounds B.kp B.near i).1)
      ⟨by exact div_le_self Real.pi_pos.le (by have := B.N_ge; have := B.kr; linarith),le_rfl⟩
    exact neg_neg_of_pos ((div_pos (by norm_num) (by positivity [B.N_pos])).trans_le hp)
  · rw [indexedSymbol_cotangent q B.n B.w ⟨hx.1,hpi⟩]
    apply mul_neg_of_pos_of_neg
    · exact div_pos (Real.sin_pos_of_pos_of_lt_pi (q.angle_mem ⟨hx.1,hpi⟩).1
        (q.angle_mem ⟨hx.1,hpi⟩).2) (Real.sin_pos_of_pos_of_lt_pi hx.1 hpi)
    · by_cases hsmall : x ≤ Real.pi/B.N
      · exact negative_bracket_small B.kp B.N_pos hx.1
          (small_angle_denominator B.n B.w hw B.N_pos B.lag_abs B.moment ⟨hx.1.le,hsmall⟩)
          (sineNumerator_abs_le_linear B.n B.w hw B.normalization B.lag_abs hx.1.le)
          (by simpa only [abs_of_pos hx.1] using (Real.abs_sin_le_abs (x := x)))
          hX B.extra_margins.1
      · exact negative_bracket_large B.N_pos
          (large_angle_denominator (n := B.n₀) (k := (k:ℤ)) (by exact_mod_cast B.period_ge) B.N_ge
            (by simpa [n,integerLag] using B.lag_abs (1:Fin 3)) B.coprime B.w
            (fun i=>(weight_bounds B.kp B.near i).1) ⟨le_of_lt (lt_of_not_ge hsmall),hx.2⟩)
          (sineNumerator_abs_le_one B.n B.w hw B.normalization x) (Real.abs_sin_le_one x) hX hA

end SourceData
end polyak.FareyPlateau.LargeCurvature
