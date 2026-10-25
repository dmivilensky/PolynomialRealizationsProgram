import polyak.General.Regions.SingleFeasible

/-! Article: Theorem A(ii). One genuine from-rest function in exactly three
real dimensions, with a planar periodic orbit and a decaying startup coordinate.
-/
namespace polyak.General.Regions
noncomputable section
open Dynamics Spectral Filter Realization
open scoped Topology

private def planeInclusion : EuclideanSpace ℂ (Fin 1) →ₗᵢ[ℝ]
    WithLp 2 (EuclideanSpace ℂ (Fin 1)×ℝ) where
  toFun x := WithLp.toLp 2 (x,0)
  map_add' x y := by apply WithLp.ofLp_injective 2; simp
  map_smul' a x := by apply WithLp.ofLp_injective 2; simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp

/-- A rational one-wave model is periodic in its planar coordinate. -/
theorem rational_wave_periodic {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k) :
    Function.Periodic (fun n : ℕ=>Waves.finitePosition (fun _ : Fin 1=>1)
      (fun _=>cosineFrequency (rationalAngle j k)) 0 (some n)) k := by
  have hω : Real.arccos ((cosineFrequency (rationalAngle j k)):ℝ)=rationalAngle j k := by
    have hω := rationalAngle_mem hj hjk
    exact Real.arccos_cos hω.1.le hω.2.le
  have hk : 0<k := by omega
  intro n
  ext i
  simp only [Waves.finitePosition_apply,NNReal.coe_one,Real.sqrt_one,one_smul,hω]
  rw [pow_add]
  have hp : Waves.z 0 (rationalAngle j k)^k=1 := by
    rw [Waves.z_pow]
    have he : (k:ℂ)*((0:ℂ)+(rationalAngle j k:ℂ)*Complex.I)=
        (j:ℂ)*(2*Real.pi*Complex.I) := by
      dsimp [rationalAngle]
      push_cast
      field_simp [show (k:ℂ)≠0 by exact_mod_cast (ne_of_gt hk)]
      ring
    simp only [Complex.ofReal_zero]
    rw [he]
    simpa only [Complex.exp_zero] using (Complex.exp_periodic.nat_mul_eq j)
  rw [hp,mul_one]

/-- The full three-dimensional startup model for any feasible threshold atom.
The linear isometry J identifies the rotating plane, so the limit statement
is stronger than a statement merely about distances to the periodic orbit. -/
theorem exists_planar_startup (q : Tuning) (c : Frequency)
    (h : Waves.MixtureFeasible (oneAtom c) (Waves.multiplierMap q.A q.B q.beta 0) 0 0) :
    ∃ f : EuclideanSpace ℝ (Fin 3)→ℝ,
      CenteredSmoothStronglyConvex q.x q.y f ∧
      ∃ x₀, x₀≠0 ∧ ∃ c₀ : ℝ,0<c₀ ∧
      ∃ J : EuclideanSpace ℂ (Fin 1)→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
        (∀ n : ℕ,c₀*‖x₀‖≤‖iterate (gradient f) 1 q.beta x₀ n‖) ∧
        Tendsto (fun n : ℕ=>iterate (gradient f) 1 q.beta x₀ n-
          J (Waves.finitePosition (fun _ : Fin 1=>1) (fun _=>c) 0 (some n))) atTop (𝓝 0) := by
  let w : Fin 1→NNReal := fun _=>1
  let a : Fin 1→Frequency := fun _=>c
  have hw : ∑ j,w j=1 := by simp [w]
  have hA : normalizedA q.x q.y 1 q.beta=q.A := by dsimp [normalizedA,Tuning.A]; ring
  have hB : normalizedB q.x q.y 1=q.B := by dsimp [normalizedB,Tuning.B]; ring
  obtain ⟨τ,Y,ψ,_,hY,hψ,hlim,hmodel⟩ := exists_startup_model q.x_pos q.x_lt_y
    (by norm_num : (0:ℝ)<1) q.beta_nonneg q.beta_lt_one (by simpa using q.y_lt)
    w a hw (by simpa only [hA,hB,oneAtom,w,a] using h)
    (fun ht=>False.elim (lt_irrefl (0:ℝ) ht))
  let E := WithLp 2 (EuclideanSpace ℂ (Fin 1)×ℝ)
  let F := denormalizeFunction q.x q.y ψ
  have hF : CenteredSmoothStronglyConvex q.x q.y F := hψ.denormalize q.x_pos q.x_lt_y
  have hdim : Module.finrank ℝ E=3 := by
    dsimp [E]
    rw [(WithLp.linearEquiv 2 ℝ (EuclideanSpace ℂ (Fin 1)×ℝ)).finrank_eq,
      Module.finrank_prod,Waves.finiteMixture_real_finrank,Module.finrank_self]
    simp
  let Q : E→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Eq.mp (congrArg (fun n=>E→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) hdim)
      (stdOrthonormalBasis ℝ E).repr.toLinearIsometry
  let G := extendObjective q.x q.y Q F
  have hG : CenteredSmoothStronglyConvex q.x q.y G := hF.extendObjective Q
  let X := startupPosition (Waves.finitePosition w a 0)
    (normalizedA q.x q.y 1 q.beta) (normalizedB q.x q.y 1) q.beta τ Y
  let x₀ := Q (X (some 0))
  let J := Q.comp planeInclusion
  have hexe (n : ℕ) : iterate (gradient G) 1 q.beta x₀ n=Q (X (some n)) := by
    rw [iterate_embedding Q (gradient F) (gradient G)
      (gradient_extendObjective_embed hF.toSmoothStronglyConvex Q) 1 q.beta (X (some 0)) n]
    exact congrArg Q (hmodel n)
  have hnorm (n : ℕ) : 1≤‖iterate (gradient G) 1 q.beta x₀ n‖ := by
    rw [hexe,Q.norm_map]
    have hh := norm_le_startupPosition (Waves.finitePosition w a 0)
      (normalizedA q.x q.y 1 q.beta) (normalizedB q.x q.y 1) q.beta τ Y n
    simpa only [Waves.norm_finitePosition w a hw,Nat.cast_mul, mul_zero,Real.exp_zero] using hh
  have hxpos : 0<‖x₀‖ := lt_of_lt_of_le zero_lt_one (by simpa using hnorm 0)
  refine ⟨G,hG,x₀,norm_pos_iff.mp hxpos,1/‖x₀‖,by positivity,J,?_,?_⟩
  · intro n
    have hmul : 1/‖x₀‖*‖x₀‖=1 := by field_simp
    rw [hmul]
    exact hnorm n
  · have hc : Continuous (fun y : ℝ=>Q (WithLp.toLp 2 ((0:EuclideanSpace ℂ (Fin 1)),Y*y))) := by
      fun_prop
    have hh := hc.continuousAt.tendsto.comp hlim
    have hz0 : (WithLp.toLp 2 ((0:EuclideanSpace ℂ (Fin 1)),(0:ℝ)):E)=0 := by
      exact WithLp.toLp_zero 2
    simp only [mul_zero,hz0,map_zero] at hh
    convert hh using 1
    funext n
    rw [hexe]
    change Q (X (some n))-Q (planeInclusion (Waves.finitePosition w a 0 (some n)))=_
    rw [← Q.map_sub]
    congr 1
    change WithLp.toLp 2 (Waves.finitePosition w a 0 (some n),
      Y*response (normalizedA q.x q.y 1 q.beta+normalizedB q.x q.y 1*τ) q.beta n)-
      WithLp.toLp 2 (Waves.finitePosition w a 0 (some n),(0:ℝ))=_
    rw [← WithLp.toLp_sub]
    congr 1
    simp

/-- Theorem A(ii), including a single actual function and start for all horizons
and convergence in norm to a k-periodic planar model. -/
theorem exists_periodic_orbit (q : Tuning) {j k : ℕ} (hcop : j.Coprime k)
    (hj : 1≤j) (hjk : 2*j<k)
    (hphase : q.angle (rationalAngle j k)≤Real.pi/k) :
    ∃ f : EuclideanSpace ℝ (Fin 3)→ℝ,
      CenteredSmoothStronglyConvex q.x q.y f ∧ ∃ x₀,x₀≠0 ∧ ∃ c₀ : ℝ,0<c₀ ∧
      ∃ J : EuclideanSpace ℂ (Fin 1)→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      ∃ orbit : ℕ→EuclideanSpace ℝ (Fin 3),Function.Periodic orbit k ∧
        (∀ n,orbit n=J (Waves.finitePosition (fun _ : Fin 1=>1)
          (fun _=>cosineFrequency (rationalAngle j k)) 0 (some n))) ∧
        (∀ n,c₀*‖x₀‖≤‖iterate (gradient f) 1 q.beta x₀ n‖) ∧
        Tendsto (fun n=>iterate (gradient f) 1 q.beta x₀ n-orbit n) atTop (𝓝 0) := by
  obtain ⟨f,hf,x₀,hx,c₀,hc,J,hb,hl⟩ := exists_planar_startup q
    (cosineFrequency (rationalAngle j k)) ((single_harmonic_feasible_iff q hcop hj hjk).mpr hphase)
  refine ⟨f,hf,x₀,hx,c₀,hc,J,fun n=>J (Waves.finitePosition (fun _ : Fin 1=>1)
    (fun _=>cosineFrequency (rationalAngle j k)) 0 (some n)),?_,fun _=>rfl,hb,hl⟩
  intro n
  exact congrArg J (rational_wave_periodic hj hjk n)

end
end polyak.General.Regions
