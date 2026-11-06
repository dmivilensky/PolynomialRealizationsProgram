import nesterov.Phase.Geometry
import nesterov.Phase.Growing
import nesterov.Realization.StartupCoordinates
import nesterov.Realization.RestRate
import polyak.General.Regions.Periodic

/-!
Article: Proposition `prop:cycles`, one fixed from-rest witness in ℝ³.
Use: the same objective serves every horizon and its trajectory approaches an
explicit periodic planar orbit, with the auxiliary coordinate tending to zero.
-/
namespace nesterov.Phase
noncomputable section
open Spectral Set Filter Realization polyak
open scoped NNReal Topology

def planeInclusion : EuclideanSpace ℂ (Fin 1)→ₗᵢ[ℝ]
    WithLp 2 (EuclideanSpace ℂ (Fin 1)×ℝ) where
  toFun x := WithLp.toLp 2 (x,0)
  map_add' x y := by apply WithLp.ofLp_injective 2; simp
  map_smul' a x := by apply WithLp.ofLp_injective 2; simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp

theorem rational_latent_periodic {j K : ℕ} (hj : 1≤j) (hjK : 2*j<K) :
    Function.Periodic (finiteLatent (fun _ : Fin 1=>(1:ℝ≥0))
      (fun _=>frequency (2*Real.pi*j/K)) 0) K := by
  exact polyak.General.Regions.rational_wave_periodic hj hjK

theorem exists_periodic_startup (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L)
    {j K : ℕ} (hK : 3≤K) (hj : 1≤j) (hjK : 2*j<K) (hcop : j.Coprime K)
    (hphase : momentumAngle q μ L (2*Real.pi*j/K)≤Real.pi/K) :
    ∃ f : EuclideanSpace ℝ (Fin 3)→ℝ,CenteredSmoothStronglyConvex μ L f ∧
      ∃ x₀,x₀≠0 ∧ ∃ c₀ : ℝ,0<c₀ ∧
        ∃ P : EuclideanSpace ℂ (Fin 1)→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
          (∀ n : ℕ,c₀*‖x₀‖≤‖Momentum.iterate (gradient f) q.beta q.tau q.stepSize x₀ n‖) ∧
          Function.Periodic (fun n : ℕ=>P (finiteLatent (fun _ : Fin 1=>(1:ℝ≥0))
            (fun _=>frequency (2*Real.pi*j/K)) 0 (n+1))) K ∧
          Tendsto (fun n : ℕ=>Momentum.iterate (gradient f) q.beta q.tau q.stepSize x₀ n-
            P (finiteLatent (fun _ : Fin 1=>(1:ℝ≥0))
              (fun _=>frequency (2*Real.pi*j/K)) 0 (n+1))) atTop (𝓝 0) := by
  let ω := 2*Real.pi*j/K
  have hω : ω∈Ioo (0:ℝ) Real.pi := polyak.General.Regions.rationalAngle_mem hj hjK
  let c := frequency ω
  let M := Momentum.method q.beta q.tau q.stepSize q.step_pos.ne'
  have hc : Real.arccos c=ω := arccos_frequency ⟨hω.1.le,hω.2.le⟩
  have hsk : 0<skew (M.symbolPair μ L 0) c := momentum_skew_pos q hμL hω
  have hθ : 0<angle (g (M.symbolPair μ L 0) c) (skew (M.symbolPair μ L 0) c) :=
    (angle_pos_lt_pi hsk).1
  have habs : |angle (g (M.symbolPair μ L 0) c) (skew (M.symbolPair μ L 0) c)|≤Real.pi/K := by
    rw [abs_of_nonneg hθ.le]
    exact hphase
  have hfeas := (singleton_feasible_of_phase hcop hK (M.symbolPair μ L 0) 0 c hc (Or.inr hsk.ne') habs).2
  let w : Fin 1→ℝ≥0 := fun _=>1
  let cs : Fin 1→Frequency := fun _=>c
  have hw : ∑ j,w j=1 := by simp [w]
  let W := finiteLatent w cs 0
  obtain ⟨lam,_,Y,f,_,hf,hlim,hx,hmodel,c₀,hc₀,hbound⟩ := exists_startup q hμ hμL hs w cs hw
    hfeas (fun ht=>False.elim (lt_irrefl (0:ℝ) ht))
  let e : WithLp 2 (EuclideanSpace ℂ (Fin 1)×ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) := by
    exact (startupCoordinates (Fin 1)).trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (by norm_num)))
  let F := polyak.extendObjective μ L e.toLinearIsometry f
  have hF : CenteredSmoothStronglyConvex μ L F := hf.extendObjective e.toLinearIsometry
  have hgrad : ∀ x,gradient F (e x)=e (gradient f x) :=
    polyak.gradient_extendObjective_embed hf.toSmoothStronglyConvex e.toLinearIsometry
  have hexe (n : ℕ) : Momentum.iterate (gradient F) q.beta q.tau q.stepSize
      (e (physical W q.beta q.tau q.stepSize lam Y 0)) n=
      e (physical W q.beta q.tau q.stepSize lam Y n) := by
    exact (Momentum.iterate_embedding e.toLinearIsometry _ _ hgrad q.beta q.tau q.stepSize
      (physical W q.beta q.tau q.stepSize lam Y 0) n).trans (congrArg e (hmodel n))
  let x₀ := e (physical W q.beta q.tau q.stepSize lam Y 0)
  let P := e.toLinearIsometry.comp planeInclusion
  have hx' : x₀≠0 := fun h=>hx (e.injective (h.trans e.map_zero.symm))
  refine ⟨F,hF,x₀,hx',c₀,hc₀,P,?_,?_,?_⟩
  · intro n
    change c₀*‖e (physical W q.beta q.tau q.stepSize lam Y 0)‖≤_
    rw [hexe,e.norm_map,e.norm_map]
    simpa only [hmodel,mul_zero,Real.exp_zero,mul_one] using hbound n
  · intro n
    change P (W (n+K+1))=P (W (n+1))
    have hp : Function.Periodic W K := rational_latent_periodic hj hjK
    rw [show n+K+1=n+1+K by omega,hp (n+1)]
  · have hcont : Continuous (fun y : ℝ=>e (WithLp.toLp 2 ((0:EuclideanSpace ℂ (Fin 1)),y))) := by fun_prop
    have hh := hcont.continuousAt.tendsto.comp hlim
    have he0 : e (WithLp.toLp 2 ((0:EuclideanSpace ℂ (Fin 1)),(0:ℝ)))=0 := e.map_zero
    rw [he0] at hh
    convert hh using 1
    funext n
    rw [hexe]
    change e (physical W q.beta q.tau q.stepSize lam Y n)-e (WithLp.toLp 2 (W (n+1),0))=
      e (WithLp.toLp 2 (0,Y*Momentum.iterate (fun x : ℝ=>lam*x) q.beta q.tau q.stepSize 1 n))
    rw [←e.map_sub]
    congr 1
    apply WithLp.ofLp_injective 2
    simp [physical]

/-- A strict rational phase inequality gives genuine divergence from rest. -/
theorem one_lt_restRate_of_strict_phase (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L)
    {j K : ℕ} (hK : 3≤K) (hj : 1≤j) (hjK : 2*j<K) (hcop : j.Coprime K)
    (hphase : momentumAngle q μ L (2*Real.pi*j/K)<Real.pi/K) :
    1<Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L := by
  let ω := 2*Real.pi*j/K
  have hω : ω∈Ioo (0:ℝ) Real.pi := polyak.General.Regions.rationalAngle_mem hj hjK
  let c := frequency ω
  let M := Momentum.method q.beta q.tau q.stepSize q.step_pos.ne'
  have hc : Real.arccos c=ω := arccos_frequency ⟨hω.1.le,hω.2.le⟩
  have hsk : 0<skew (M.symbolPair μ L 0) c := momentum_skew_pos q hμL hω
  have habs : |angle (g (M.symbolPair μ L 0) c) (skew (M.symbolPair μ L 0) c)|<Real.pi/K := by
    rw [abs_of_nonneg (angle_pos_lt_pi hsk).1.le]
    exact hphase
  obtain ⟨t,ht,hg,hfeas⟩ := exists_growing_singleton M μ L hcop hK c hc (Or.inr hsk.ne') habs
  have hr := Realization.exp_le_momentumRestRate_of_feasible q hμ hμL hs
    (fun _ : Fin 1=>(1:ℝ≥0)) (fun _=>c) (by simp) hfeas (fun _=>by
      change |(0:ℝ)|<meanG (singletonSpectrum c) (M.symbolPair μ L t)
      simpa using hg)
  have hp : (1:ℝ)<Real.exp t := by simpa using Real.exp_lt_exp.mpr ht
  exact hp.trans_le hr

end
end nesterov.Phase
