import nesterov.Spectral.Finite
import nesterov.Realization.Potential

/-!
Article: Lemma `lem:startup`, uniform control of the exceptional initial pairs.
Use: finite waves are bounded when t≤0; positive t uses the exact strict
minimizer slack, with the query amplitude included in the norm bound.
-/
namespace nesterov.Realization
noncomputable section
open nesterov.Spectral polyak polyak.Interpolation polyak.Realization
open scoped BigOperators NNReal
variable {J : Type*} [Fintype J]

theorem finite_stateNorm (M : StationaryMethod) (w : J→ℝ≥0) (c : J→Frequency)
    (hw : ∑ j,w j=1) (t : ℝ) (k : ℕ) :
    M.stateNorm (finiteLatent w c t) k=Real.exp (k*t)*M.stateNorm (finiteLatent w c t) 0 := by
  have he (j : Fin M.memory) : Real.exp (((k+j.val:ℕ):ℝ)*t)=
      Real.exp (k*t)*Real.exp (j.val*t) := by rw [Nat.cast_add,add_mul,Real.exp_add]
  have hs : M.stateNorm (finiteLatent w c t) k^2=
      (Real.exp (k*t)*M.stateNorm (finiteLatent w c t) 0)^2 := by
    rw [mul_pow,M.stateNorm_sq,M.stateNorm_sq]
    simp only [norm_finiteLatent w c hw,he,mul_pow,Nat.zero_add,Finset.mul_sum]
  exact (sq_eq_sq₀ (M.stateNorm_nonneg _ _)
    (mul_nonneg (Real.exp_pos _).le (M.stateNorm_nonneg _ _))).mp hs

theorem finite_originSlack (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (a : SymbolPair) (C t δ : ℝ) (k : ℕ) :
    originSlack (finitePosition w c a t (some k)) (finiteGradient w c a t (some k))
      (mixtureValue (finiteSpectrum w c hw) a C t (some k)) δ=
      (1/4:ℝ)*Real.exp (2*k*t)*(meanG (finiteSpectrum w c hw) a+δ*C) := by
  have hR : datumR (finitePosition w c a t) (finiteGradient w c a t) none (some k)=
      datumR (mixturePosition (finiteSpectrum w c hw) a t)
        (mixtureGradient (finiteSpectrum w c hw) a t) none (some k) :=
    polyak.Waves.datumR_finiteLift w c hw (positionMap a t) (gradientMap a t) none (some k)
  have hT : datumT (finitePosition w c a t) (finiteGradient w c a t)
        (mixtureValue (finiteSpectrum w c hw) a C t) none (some k)=
      datumT (mixturePosition (finiteSpectrum w c hw) a t)
        (mixtureGradient (finiteSpectrum w c hw) a t)
        (mixtureValue (finiteSpectrum w c hw) a C t) none (some k) :=
    polyak.Waves.datumT_finiteLift w c hw (positionMap a t) (gradientMap a t)
      (mixtureValue (finiteSpectrum w c hw) a C t) none (some k)
  have hh := mixture_star_slack (finiteSpectrum w c hw) a C t δ k
  rw [←hR,←hT] at hh
  simpa only [datumR,datumT,finitePosition_none,finiteGradient_none,
    mixtureValue_none,sub_zero,zero_add,originSlack] using hh

theorem finite_startup_control (M : StationaryMethod) (μ L : ℝ)
    (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1) {C t : ℝ}
    (hstrict : 0<t → |C|<meanG (finiteSpectrum w c hw) (M.symbolPair μ L t)) :
    (∃ B : ℝ,∀ k,‖finitePosition w c (M.symbolPair μ L t) t (some k)‖≤B) ∨
      ∃ η : ℝ,0<η ∧ ∀ k δ,δ=1 ∨ δ= -1 →
        η*‖finitePosition w c (M.symbolPair μ L t) t (some k)‖^2≤
          originSlack (finitePosition w c (M.symbolPair μ L t) t (some k))
            (finiteGradient w c (M.symbolPair μ L t) t (some k))
            (mixtureValue (finiteSpectrum w c hw) (M.symbolPair μ L t) C t (some k)) δ := by
  let a := M.symbolPair μ L t
  let B := 1+M.queryGain*M.stateNorm (finiteLatent w c t) 0
  have hB : 0<B := by
    dsimp [B]
    nlinarith [mul_nonneg M.queryGain_nonneg (M.stateNorm_nonneg (finiteLatent w c t) 0)]
  have hbound (k : ℕ) : ‖finitePosition w c a t (some k)‖≤B*Real.exp (k*t) := by
    rw [←query_finiteLatent M μ L]
    have hh := M.norm_query_le (finiteLatent w c t) k
    rw [finite_stateNorm M w c hw] at hh
    dsimp [B]
    nlinarith [Real.exp_pos (k*t)]
  by_cases ht : t≤0
  · left
    refine ⟨B,fun k=> (hbound k).trans ?_⟩
    have he : Real.exp ((k:ℝ)*t)≤1 := by
      simpa using Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ht)
    nlinarith
  · right
    have hs := hstrict (lt_of_not_ge ht)
    let η := (meanG (finiteSpectrum w c hw) a-|C|)/(4*B^2)
    have hη : 0<η := by dsimp [η]; exact div_pos (sub_pos.mpr hs) (by positivity)
    refine ⟨η,hη,fun k δ hδ=>?_⟩
    rw [finite_originSlack]
    have hh := pow_le_pow_left₀ (norm_nonneg _) (hbound k) 2
    have he : Real.exp ((k:ℝ)*t)^2=Real.exp (2*k*t) := by
      rw [←Real.exp_nat_mul]
      congr 1
      ring
    rw [mul_pow,he] at hh
    have hb := mul_le_mul_of_nonneg_left hh hη.le
    have hηB : η*B^2=(meanG (finiteSpectrum w c hw) a-|C|)/4 := by
      dsimp [η]
      field_simp
    rw [←mul_assoc,hηB] at hb
    have hδC : -|C|≤δ*C := by rcases hδ with rfl | rfl <;> nlinarith [neg_abs_le C,le_abs_self C]
    nlinarith only [hb,mul_le_mul_of_nonneg_left hδC (Real.exp_pos (2*k*t)).le]

end
end nesterov.Realization
