import polyak.Realization.Finite
import polyak.Realization.Actual

/-!
Article: Appendix A, Lemma startup and spectralgeneral(c).
Use: a single genuine from-rest example in exactly 2r+1 real dimensions for every horizon.
Proof: interpolate the corrected orthogonal wave table, execute the true gradient algorithm,
and transport the complete finite-dimensional Hilbert space through an orthonormal basis.
-/

namespace polyak.Realization
noncomputable section
open Interpolation Waves Spectral Dynamics Filter
open scoped Topology

variable {J : Type*} [Fintype J]

/-- Article: one-coordinate startup with its complete trajectory model.
Use: retain the r complex waves and the single decaying scalar coordinate explicitly. -/
theorem exists_startup_model {μ L α β C t : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0<α) (hβ : 0 ≤ β) (hβ1 : β<1) (hquad : α*L<2*(1+β))
    (w : J → NNReal) (c : J → Frequency) (hw : ∑ j,w j=1)
    (h : MixtureFeasible (finiteSpectrum w c hw)
      (multiplierMap (normalizedA μ L α β) (normalizedB μ L α) β t) C t)
    (hstrict : 0<t → |C|<spectrumG (finiteSpectrum w c hw)
      (multiplierMap (normalizedA μ L α β) (normalizedB μ L α) β t)) :
    ∃ τ Y : ℝ, ∃ ψ : WithLp 2 (EuclideanSpace ℂ J × ℝ) → ℝ,
      |τ|<1 ∧ 0<Y ∧ NormalizedSmooth ψ ∧
      Tendsto (response (normalizedA μ L α β+normalizedB μ L α*τ) β) atTop (𝓝 0) ∧
      ∀ N : ℕ, iterate (gradient (denormalizeFunction μ L ψ)) α β
        (startupPosition (finitePosition w c t) (normalizedA μ L α β) (normalizedB μ L α) β τ Y (some 0)) N=
          startupPosition (finitePosition w c t) (normalizedA μ L α β) (normalizedB μ L α) β τ Y (some N) := by
  let A := normalizedA μ L α β
  let B := normalizedB μ L α
  let m := multiplierMap A B β t
  let x := finitePosition w c t
  let σ := finiteGradient w c m t
  let v := finiteValue w c m C t
  have hB : 0<B := by dsimp [B,normalizedB]; positivity
  obtain ⟨τ,Y,ψ,hτ,hY,hψ,hlim,hdata⟩ := exists_startup_potential hB hβ hβ1
    (normalizedA_abs_add_B_lt hμ hα hquad) x σ v (finite_tableFeasible w c hw h)
    (finitePosition_none w c t) (finiteGradient_none w c m t) (finiteValue_none w c m C t)
    (finite_startup_control w c hw hstrict) (initialGradient x A B β)
  refine ⟨τ,Y,ψ,hτ,hY,hψ,hlim,fun N => ?_⟩
  exact startup_iterate x σ hψ (ne_of_gt hB) (fun i => (hdata i).2)
    (finite_recurrence w c A B β t (ne_of_gt hB)) N

/-- Article: one-coordinate initialization and spectralgeneral(c).
Use: one function and one nonzero from-rest start realize the lower bound on all horizons. -/
theorem exists_startup {μ L α β C t : ℝ} (hμ : 0<μ) (hL : μ<L)
    (hα : 0<α) (hβ : 0 ≤ β) (hβ1 : β<1) (hquad : α*L<2*(1+β))
    (w : J → NNReal) (c : J → Frequency) (hw : ∑ j,w j=1)
    (h : MixtureFeasible (finiteSpectrum w c hw)
      (multiplierMap (normalizedA μ L α β) (normalizedB μ L α) β t) C t)
    (hstrict : 0<t → |C|<spectrumG (finiteSpectrum w c hw)
      (multiplierMap (normalizedA μ L α β) (normalizedB μ L α) β t)) :
    ∃ f : EuclideanSpace ℝ (Fin (2*Fintype.card J+1)) → ℝ,
      CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀, x₀≠0 ∧ ∃ c₀ : ℝ,0<c₀ ∧ ∀ N : ℕ,
        c₀*Real.exp (N*t)*‖x₀‖ ≤ ‖iterate (gradient f) α β x₀ N‖ := by
  obtain ⟨τ,Y,ψ,_,_,hψ,_,hmodel⟩ := exists_startup_model hμ hL hα hβ hβ1 hquad w c hw h hstrict
  let E := WithLp 2 (EuclideanSpace ℂ J × ℝ)
  let F := denormalizeFunction μ L ψ
  have hF : CenteredSmoothStronglyConvex μ L F := hψ.denormalize hμ hL
  let Q := (stdOrthonormalBasis ℝ E).repr.toLinearIsometry
  let G := extendObjective μ L Q F
  have hG : CenteredSmoothStronglyConvex μ L G := hF.extendObjective Q
  let X := startupPosition (finitePosition w c t) (normalizedA μ L α β) (normalizedB μ L α) β τ Y
  let x₀ := Q (X (some 0))
  have hnorm (N : ℕ) : Real.exp (N*t) ≤ ‖iterate (gradient G) α β x₀ N‖ := by
    rw [iterate_embedding Q (gradient F) (gradient G)
      (gradient_extendObjective_embed hF.toSmoothStronglyConvex Q) α β (X (some 0)) N,Q.norm_map,hmodel N]
    exact (norm_finitePosition w c hw t N).symm ▸ norm_le_startupPosition (finitePosition w c t) _ _ _ _ _ N
  have hxpos : 0<‖x₀‖ := by
    have hh := hnorm 0
    simp only [Nat.cast_zero,zero_mul,Real.exp_zero,iterate_zero] at hh
    linarith
  have hxne : x₀≠0 := norm_pos_iff.mp hxpos
  have hdim : Module.finrank ℝ E=2*Fintype.card J+1 := by
    dsimp [E]
    rw [(WithLp.linearEquiv 2 ℝ (EuclideanSpace ℂ J × ℝ)).finrank_eq,
      Module.finrank_prod,finiteMixture_real_finrank,Module.finrank_self]
  have hresult : ∃ f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ,
      CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀,x₀≠0 ∧ ∃ c₀ : ℝ,0<c₀ ∧ ∀ N : ℕ,
        c₀*Real.exp (N*t)*‖x₀‖ ≤ ‖iterate (gradient f) α β x₀ N‖ := by
    refine ⟨G,hG,x₀,hxne,1/‖x₀‖,by positivity,fun N => ?_⟩
    have he : (1/‖x₀‖)*Real.exp (N*t)*‖x₀‖=Real.exp (N*t) := by
      field_simp
    rw [he]
    exact hnorm N
  rw [hdim] at hresult
  exact hresult

end
end polyak.Realization
