import polyak.Realization.Potential
import polyak.Waves.Finite
import polyak.Waves.Dynamics

/-!
Article: Appendix A, finite spectral data in Lemma startup.
Use: discharge every hypothesis of the general one-coordinate interpolation construction.
Proof: exact finite-mixture interpolation and the strict minimizer spectral slack.
-/

namespace polyak.Realization
noncomputable section
open Interpolation Waves Spectral

variable {J : Type*} [Fintype J]

omit [Fintype J] in
/-- Article: the finite mode minimizer position. -/
@[simp] theorem finitePosition_none (w : J → NNReal) (c : J → Frequency) (t : ℝ) :
    finitePosition w c t none=0 := by
  have he : positionMap t none=0 := by ext; rfl
  simp [finitePosition,he]

omit [Fintype J] in
/-- Article: the finite mode minimizer gradient. -/
@[simp] theorem finiteGradient_none (w : J → NNReal) (c : J → Frequency)
    (m : C(Frequency,ℂ)) (t : ℝ) : finiteGradient w c m t none=0 := by
  have he : gradientMap m t none=0 := by ext; simp [gradientMap,positionMap,position]
  simp [finiteGradient,he]

/-- Article: the finite mode minimizer value. -/
@[simp] theorem finiteValue_none (w : J → NNReal) (c : J → Frequency)
    (m : C(Frequency,ℂ)) (C t : ℝ) : finiteValue w c m C t none=0 := by
  simp [finiteValue,valueMap,value]

/-- Article: all stationary mode interpolation inequalities. -/
theorem finite_tableFeasible (w : J → NNReal) (c : J → Frequency) (hw : ∑ j,w j=1)
    {m : C(Frequency,ℂ)} {C t : ℝ} (h : MixtureFeasible (finiteSpectrum w c hw) m C t) :
    TableFeasible (finitePosition w c t) (finiteGradient w c m t) (finiteValue w c m C t) := by
  obtain ⟨ψ,hψ,hdata⟩ := (finite_interpolation_iff w c hw m C t).mpr h
  have he := hψ.tableFeasible (finitePosition w c t)
  have hv : (fun i => ψ (finitePosition w c t i))=finiteValue w c m C t := funext (fun i => (hdata i).1)
  have hg : (fun i => gradient ψ (finitePosition w c t i))=finiteGradient w c m t := funext (fun i => (hdata i).2)
  rwa [hv,hg] at he

omit [Fintype J] in
/-- Article: finite modes satisfy the actual normalized recurrence. -/
theorem finite_recurrence (w : J → NNReal) (c : J → Frequency) (A B β t : ℝ)
    (hB : B≠0) (k : ℕ) :
    finitePosition w c t (some (k+2))=A • finitePosition w c t (some (k+1))+
      B • finiteGradient w c (multiplierMap A B β t) t (some (k+1))-
      β • finitePosition w c t (some k) := by
  unfold finitePosition finiteGradient
  rw [positionMap_recurrence A B β t hB k,map_sub,map_add,map_smul,map_smul,map_smul]

/-- Article: bounded or growing modes. Use: strictness is used only when the exponent is positive. -/
theorem finite_startup_control (w : J → NNReal) (c : J → Frequency) (hw : ∑ j,w j=1)
    {m : C(Frequency,ℂ)} {C t : ℝ}
    (hstrict : 0<t → |C|<spectrumG (finiteSpectrum w c hw) m) :
    (∀ k, ‖finitePosition w c t (some k)‖  ≤  1) ∨
      ∃ η : ℝ,0<η ∧ ∀ k δ,δ=1 ∨ δ= -1 →
        η*‖finitePosition w c t (some k)‖^2  ≤ 
          originSlack (finitePosition w c t (some k)) (finiteGradient w c m t (some k))
            (finiteValue w c m C t (some k)) δ := by
  by_cases ht : t  ≤  0
  · left
    intro k
    rw [norm_finitePosition w c hw]
    exact (Real.exp_le_exp.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ht)).trans_eq Real.exp_zero
  · right
    have hs := hstrict (lt_of_not_ge ht)
    let η := (spectrumG (finiteSpectrum w c hw) m-|C|)/4
    refine ⟨η,by dsimp [η]; positivity,fun k δ hδ => ?_⟩
    have he := finite_star_slack w c hw m C t δ k
    simp only [datumR,datumT,finitePosition_none,finiteGradient_none,finiteValue_none,
      sub_zero,zero_add] at he
    change originSlack (finitePosition w c t (some k)) (finiteGradient w c m t (some k))
      (finiteValue w c m C t (some k)) δ = _ at he
    rw [he,norm_finitePosition w c hw]
    have hex : Real.exp (k*t)^2=Real.exp (2*k*t) := by
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [hex]
    have hδC : -|C|  ≤  δ*C := by rcases hδ with rfl | rfl <;> nlinarith [neg_abs_le C,le_abs_self C]
    dsimp [η]
    nlinarith [mul_le_mul_of_nonneg_left hδC (Real.exp_pos (2*k*t)).le]

end
end polyak.Realization
