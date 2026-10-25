import polyak.Realization.Startup
import polyak.Levels.Program.Pinning

/-! Article: the actual finite periodic model in exactly 2r+1 real dimensions. -/
namespace polyak.Levels
noncomputable section
open Dynamics Spectral Filter Realization
open scoped Topology
variable {J : Type*} [Fintype J]

private def modeInclusion : EuclideanSpace ℂ J →ₗᵢ[ℝ]
    WithLp 2 (EuclideanSpace ℂ J×ℝ) where
  toFun x := WithLp.toLp 2 (x,0)
  map_add' x y := by apply WithLp.ofLp_injective 2; simp
  map_smul' a x := by apply WithLp.ofLp_injective 2; simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp

theorem exists_finite_threshold_startup {μ L α β : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β))
    (w : J→NNReal) (a : J→Spectral.Frequency) (hw : ∑j,w j=1)
    (h : Waves.MixtureFeasible (Waves.finiteSpectrum w a hw)
      (Waves.multiplierMap (normalizedA μ L α β) (normalizedB μ L α) β 0) 0 0) :
    ∃ f : EuclideanSpace ℝ (Fin (2*Fintype.card J+1))→ℝ,
      CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀,x₀≠0 ∧ ∃ c₀ : ℝ,0<c₀ ∧
      ∃ Q : EuclideanSpace ℂ J→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2*Fintype.card J+1)),
        (∀ n : ℕ,c₀*‖x₀‖≤‖iterate (gradient f) α β x₀ n‖) ∧
        Tendsto (fun n : ℕ=>iterate (gradient f) α β x₀ n-
          Q (Waves.finitePosition w a 0 (some n))) atTop (𝓝 0) := by
  obtain ⟨τ,Y,ψ,_,hY,hψ,hlim,hmodel⟩ := exists_startup_model hμ hL hα hβ hβ1 hquad
    w a hw h
    (fun ht=>False.elim (lt_irrefl (0:ℝ) ht))
  let E := WithLp 2 (EuclideanSpace ℂ J×ℝ)
  let F := denormalizeFunction μ L ψ
  have hF : CenteredSmoothStronglyConvex μ L F := hψ.denormalize hμ hL
  have hdim : Module.finrank ℝ E=2*Fintype.card J+1 := by
    dsimp [E]
    rw [(WithLp.linearEquiv 2 ℝ (EuclideanSpace ℂ J×ℝ)).finrank_eq,
      Module.finrank_prod,Waves.finiteMixture_real_finrank,Module.finrank_self]
  let Q : E→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2*Fintype.card J+1)) :=
    Eq.mp (congrArg (fun n=>E→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) hdim)
      (stdOrthonormalBasis ℝ E).repr.toLinearIsometry
  let G := extendObjective μ L Q F
  have hG : CenteredSmoothStronglyConvex μ L G := hF.extendObjective Q
  let X := startupPosition (Waves.finitePosition w a 0)
    (normalizedA μ L α β) (normalizedB μ L α) β τ Y
  let x₀ := Q (X (some 0))
  let R := Q.comp modeInclusion
  have hexe (n : ℕ) : iterate (gradient G) α β x₀ n=Q (X (some n)) := by
    rw [iterate_embedding Q (gradient F) (gradient G)
      (gradient_extendObjective_embed hF.toSmoothStronglyConvex Q) α β (X (some 0)) n]
    exact congrArg Q (hmodel n)
  have hnorm (n : ℕ) : 1≤‖iterate (gradient G) α β x₀ n‖ := by
    rw [hexe,Q.norm_map]
    have hh := norm_le_startupPosition (Waves.finitePosition w a 0)
      (normalizedA μ L α β) (normalizedB μ L α) β τ Y n
    simpa only [Waves.norm_finitePosition w a hw,Nat.cast_mul, mul_zero,Real.exp_zero] using hh
  have hxpos : 0<‖x₀‖ := lt_of_lt_of_le zero_lt_one (by simpa using hnorm 0)
  refine ⟨G,hG,x₀,norm_pos_iff.mp hxpos,1/‖x₀‖,by positivity,R,?_,?_⟩
  · intro n
    have hmul : 1/‖x₀‖*‖x₀‖=1 := by field_simp
    rw [hmul]
    exact hnorm n
  · have hc : Continuous (fun y : ℝ=>Q (WithLp.toLp 2 ((0:EuclideanSpace ℂ J),Y*y))) := by
      fun_prop
    have hh := hc.continuousAt.tendsto.comp hlim
    have hz0 : (WithLp.toLp 2 ((0:EuclideanSpace ℂ J),(0:ℝ)):E)=0 := by
      exact WithLp.toLp_zero 2
    simp only [mul_zero,hz0,map_zero] at hh
    convert hh using 1
    funext n
    rw [hexe]
    change Q (X (some n))-Q (modeInclusion (Waves.finitePosition w a 0 (some n)))=_
    rw [← Q.map_sub]
    congr 1
    change WithLp.toLp 2 (Waves.finitePosition w a 0 (some n),
      Y*response (normalizedA μ L α β+normalizedB μ L α*τ) β n)-
      WithLp.toLp 2 (Waves.finitePosition w a 0 (some n),(0:ℝ))=_
    rw [← WithLp.toLp_sub]
    congr 1
    simp


omit [Fintype J] in
/-- Roots of unity give a periodic finite-wave orbit, independently of the
weights and without any coprimality restriction. -/
theorem finite_wave_periodic (w : J→NNReal) (a : J→Spectral.Frequency) (k : ℕ)
    (hp : ∀j,Waves.z 0 (Real.arccos (a j:ℝ))^k=1) :
    Function.Periodic (fun n : ℕ=>Waves.finitePosition w a 0 (some n)) k := by
  intro n
  ext j
  simp only [Waves.finitePosition_apply,pow_add,hp,mul_one]

/-- The full periodic conclusion in dimension 2r+1, for one actual objective
and one actual from-rest start on all horizons. -/
theorem exists_finite_periodic_orbit {μ L α β : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β))
    (w : J→NNReal) (a : J→Spectral.Frequency) (hw : ∑j,w j=1)
    (h : Waves.MixtureFeasible (Waves.finiteSpectrum w a hw)
      (Waves.multiplierMap (normalizedA μ L α β) (normalizedB μ L α) β 0) 0 0)
    (k : ℕ) (hp : ∀j,Waves.z 0 (Real.arccos (a j:ℝ))^k=1) :
    ∃ f : EuclideanSpace ℝ (Fin (2*Fintype.card J+1))→ℝ,
      CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀,x₀≠0 ∧ ∃ c₀ : ℝ,0<c₀ ∧
      ∃ orbit : ℕ→EuclideanSpace ℝ (Fin (2*Fintype.card J+1)),
        Function.Periodic orbit k ∧
        (∀n,c₀*‖x₀‖≤‖iterate (gradient f) α β x₀ n‖) ∧
        Tendsto (fun n=>iterate (gradient f) α β x₀ n-orbit n) atTop (𝓝 0) := by
  obtain ⟨f,hf,x₀,hx,c₀,hc,Q,hb,hl⟩:=
    exists_finite_threshold_startup hμ hL hα hβ hβ1 hquad w a hw h
  refine ⟨f,hf,x₀,hx,c₀,hc,fun n=>Q (Waves.finitePosition w a 0 (some n)),?_,hb,hl⟩
  intro n
  exact congrArg Q (finite_wave_periodic w a k hp n)

end
end polyak.Levels
