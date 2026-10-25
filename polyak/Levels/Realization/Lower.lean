import polyak.Levels.Realization.Model
import polyak.Levels.Realization.Compression
import polyak.Realization.Rate

/-! Article: exact threshold criterion (b).
A single arbitrary-spectrum Hilbert startup has one positive initial
normalization constant for every horizon. Finite-prefix compression gives
an actual Euclidean instance at each horizon and hence the uniform source
lower bound W_N≥c>0, before passing to the original rate. -/

namespace polyak.Levels.Realization
noncomputable section
open Waves Spectral Dynamics

theorem norm_continuous_startup_zero_sq (ν : Spectrum) (A B β τ Y : ℝ) :
    ‖polyak.Realization.startupPosition (mixturePosition ν 0) A B β τ Y (some 0)‖^2=
      1+Y^2 := by
  rw [polyak.Realization.startupPosition,polyak.Realization.productPosition,
    WithLp.prod_norm_sq_eq_of_L2]
  change ‖mixturePosition ν 0 (some 0)‖^2+
    ‖polyak.Realization.scalarPosition (polyak.Realization.response (A+B*τ) β) Y (some 0)‖^2=1+Y^2
  simp only [norm_mixturePosition,Nat.cast_zero,mul_zero,Real.exp_zero,one_pow,
    polyak.Realization.scalarPosition,polyak.Realization.response_zero,mul_one,
    Real.norm_eq_abs,sq_abs]

theorem threshold_spectrum_worstAll_lower {μ L α β : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β)) (ν : Spectrum)
    (h : MixtureFeasible ν (multiplierMap (normalizedA μ L α β)
      (normalizedB μ L α) β 0) 0 0) :
    ∃ c : ℝ,0<c ∧ ∀ N : ℕ,c≤worstAll μ L α β N := by
  obtain ⟨τ,Y,ψ,_,_,hψ,_,hmodel⟩:=exists_continuous_startup_model hμ hL hα hβ hβ1 hquad ν h
  let X:=polyak.Realization.startupPosition (mixturePosition ν 0)
    (normalizedA μ L α β) (normalizedB μ L α) β τ Y
  have hnorm (n : ℕ) : 1≤‖iterate (gradient (denormalizeFunction μ L ψ)) α β (X (some 0)) n‖ := by
    rw [hmodel]
    have hh:=polyak.Realization.norm_le_startupPosition (mixturePosition ν 0)
      (normalizedA μ L α β) (normalizedB μ L α) β τ Y n
    simpa only [norm_mixturePosition,mul_zero,Real.exp_zero] using hh
  have hxpos : 0<‖X (some 0)‖:=lt_of_lt_of_le zero_lt_one (by simpa using hnorm 0)
  have hx : X (some 0)≠0:=norm_pos_iff.mp hxpos
  refine ⟨1/‖X (some 0)‖,by positivity,fun N=>?_⟩
  obtain ⟨d,hd,F,hF,y₀,hy₀,hy⟩:=compress_normalized_run hψ hμ hL α β (X (some 0)) hx N
  have hn₀ : ‖y₀‖=‖X (some 0)‖:=by simpa using hy 0 (by omega)
  have hnN : 1≤‖iterate (gradient F) α β y₀ N‖:=by
    rw [hy N le_rfl]
    exact hnorm N
  have hmin : ∀ y,F 0≤F y:=
    (hF.toSmoothStronglyConvex.minimizer_iff 0).mpr hF.gradient_zero
  have hr : ‖iterate (gradient F) α β y₀ N‖/‖y₀‖∈ratios μ L α β d N := by
    refine ⟨F,hF.toSmoothStronglyConvex,0,y₀,hmin,hy₀,?_⟩
    simp only [sub_zero]
  calc
    1/‖X (some 0)‖≤‖iterate (gradient F) α β y₀ N‖/‖y₀‖ := by
      rw [hn₀]
      exact div_le_div_of_nonneg_right hnN hxpos.le
    _≤worstAll μ L α β N:=le_csSup
      (allRatios_bddAbove hμ hL hα.le hβ N) (Set.mem_insert_of_mem _ ⟨d,hd,hr⟩)

theorem one_le_rate_of_threshold_spectrum {μ L α β : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β)) (ν : Spectrum)
    (h : MixtureFeasible ν (multiplierMap (normalizedA μ L α β)
      (normalizedB μ L α) β 0) 0 0) : 1≤rate μ L α β := by
  obtain ⟨c,hc,hl⟩:=threshold_spectrum_worstAll_lower hμ hL hα hβ hβ1 hquad ν h
  have hh:=polyak.Realization.exp_le_rate_of_example (t:=0) hμ hL hα.le hβ hc
    (by simpa only [mul_zero,Real.exp_zero,mul_one] using hl)
  simpa only [Real.exp_zero] using hh

end
end polyak.Levels.Realization
