import polyak.Realization.Rate
import polyak.Growth.Quadratic
import polyak.General.Roots

/-! Article: Theorem B, the unconditional quadratic lower bound for the
original from-rest problem. A genuine finite spectrum is realized by startup;
free-state envelopes are not substituted for the original rate. -/
namespace polyak.General.Regions
noncomputable section
open Dynamics Spectral

private theorem curvatureRoot_norm_le_originalRate_upper {μ L α β lam : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β)) (hlam : lam∈Set.Icc μ L) (z : ℂ)
    (hz : z^2-((1+β-α*lam : ℝ):ℂ)*z+(β:ℂ)=0) (hzi : 0≤z.im) :
    ‖z‖≤rate μ L α β := by
  by_cases hzne : z=0
  · simpa only [hzne,norm_zero] using rate_nonneg hμ hL hα.le hβ
  have hn : 0<‖z‖ := norm_pos_iff.mpr hzne
  have hns : ‖z‖<1 := heavyBall_root_norm_lt_one hμ hα hβ hβ1 hlam.1 hlam.2 hquad hz
  let t := Real.log ‖z‖
  let c₀ : Frequency := ⟨Real.cos z.arg,Real.neg_one_le_cos _,Real.cos_le_one _⟩
  let d := (L+μ-2*lam)/(L-μ)
  have hd : |d|≤1 := by
    rw [abs_le]
    constructor
    · exact (le_div_iff₀ (sub_pos.mpr hL)).mpr (by linarith [hlam.2])
    · exact (div_le_iff₀ (sub_pos.mpr hL)).mpr (by linarith [hlam.1])
  have har : Real.arccos (c₀:ℝ)=z.arg :=
    Real.arccos_cos (Complex.arg_nonneg_iff.mpr hzi) (Complex.arg_le_pi _)
  have hwave : Waves.z t z.arg=z := by
    change Complex.exp ((Real.log ‖z‖:ℂ)+(z.arg:ℂ)*Complex.I)=z
    exact Complex.exp_log hzne
  have ha : normalizedA μ L α β+normalizedB μ L α*d=1+β-α*lam := by
    dsimp [normalizedA,normalizedB,d]
    field_simp [ne_of_gt (sub_pos.mpr hL)]
    ring
  have hB : (normalizedB μ L α:ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (show 0<normalizedB μ L α by unfold normalizedB; positivity))
  have hm : Waves.multiplierMap (normalizedA μ L α β) (normalizedB μ L α) β t c₀=(d:ℂ) := by
    change Waves.multiplier (normalizedA μ L α β) (normalizedB μ L α) β t (Real.arccos c₀)=(d:ℂ)
    rw [har]
    unfold Waves.multiplier
    rw [hwave,div_eq_iff hB]
    have hid : z+(β:ℂ)/z-(normalizedA μ L α β:ℂ)=
        (z^2+(β:ℂ)-(normalizedA μ L α β:ℂ)*z)/z := by field_simp
    rw [hid]
    apply (div_eq_iff hzne).mpr
    have ha' : (normalizedA μ L α β:ℂ)+(normalizedB μ L α:ℂ)*(d:ℂ)=(1+β-α*lam:ℝ) := by
      exact_mod_cast ha
    linear_combination hz-ha'*z
  let w : Fin 1→NNReal := fun _=>1
  let c : Fin 1→Frequency := fun _=>c₀
  have hw : ∑ j,w j=1 := by simp [w]
  have ht : t<0 := Real.log_neg hn hns
  have hfeas : Waves.MixtureFeasible (Waves.finiteSpectrum w c hw)
      (Waves.multiplierMap (normalizedA μ L α β) (normalizedB μ L α) β t) 0 t := by
    have hg : 0≤1-d^2 := by nlinarith [(sq_le_one_iff_abs_le_one d).mpr hd]
    constructor
    · simp only [Waves.spectrumG,Waves.finiteSpectrum_integral,c,w,Fin.sum_univ_one,
        hm,Complex.normSq_ofReal,NNReal.coe_one,one_mul,abs_zero]
      simpa only [pow_two] using hg
    · intro n _
      have hp : 0≤(1-d^2)*(Real.cosh (n*t)-Real.cos (n*Real.arccos c₀)) :=
        mul_nonneg hg (by linarith [Real.one_le_cosh (n*t),Real.cos_le_one (n*Real.arccos c₀)])
      simpa only [Waves.spectrumA,Waves.spectrumB,Waves.finiteSpectrum_integral,c,w,
        Fin.sum_univ_one,hm,Complex.normSq_ofReal,Complex.ofReal_im,NNReal.coe_one,
        one_mul,mul_zero,zero_mul,sub_zero,add_zero,pow_two] using And.intro hp hp
  have hrate := Realization.exp_le_originalRate hμ hL hα hβ hβ1 hquad w c hw hfeas
    (fun hp=>False.elim (not_lt_of_ge ht.le hp))
  simpa only [t,Real.exp_log hn] using hrate

/-- Every quadratic characteristic root supplies its modulus as an actual rate lower bound. -/
theorem curvatureRoot_norm_le_originalRate {μ L α β lam : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β)) (hlam : lam∈Set.Icc μ L) (z : ℂ)
    (hz : z^2-((1+β-α*lam : ℝ):ℂ)*z+(β:ℂ)=0) :
    ‖z‖≤rate μ L α β := by
  by_cases hi : 0≤z.im
  · exact curvatureRoot_norm_le_originalRate_upper hμ hL hα hβ hβ1 hquad hlam z hz hi
  · have hz' : (starRingEnd ℂ z)^2-((1+β-α*lam : ℝ):ℂ)*(starRingEnd ℂ z)+(β:ℂ)=0 := by
      simpa only [map_sub,map_add,map_pow,map_mul,Complex.conj_ofReal,map_zero] using
        congrArg (starRingEnd ℂ) hz
    have hh := curvatureRoot_norm_le_originalRate_upper hμ hL hα hβ hβ1 hquad hlam
      (starRingEnd ℂ z) hz' (by simpa using le_of_lt (neg_pos.mpr (lt_of_not_ge hi)))
    simpa only [Complex.norm_conj] using hh

/-- Theorem B's lower bound refers to the exact original limsup, in all tunings. -/
theorem quadraticRate_le_originalRate {μ L α β : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β)) : quadraticRate μ L α β≤rate μ L α β := by
  obtain ⟨lam,hlam,z,hz,hr⟩ := (quadraticRate_isGreatest hμ hL hα hβ hβ1 hquad).1
  rw [hr]
  exact curvatureRoot_norm_le_originalRate hμ hL hα hβ hβ1 hquad hlam z hz

/-- The same lower bound in the phase diagram's dimensionless source coordinates. -/
theorem rhoQ_le_rate (q : Tuning) : q.rhoQ≤rate q.x q.y 1 q.beta := by
  rw [← q.quadraticRate_eq]
  exact quadraticRate_le_originalRate q.x_pos q.x_lt_y (by norm_num) q.beta_nonneg
    q.beta_lt_one (by simpa using q.y_lt)

end
end polyak.General.Regions
