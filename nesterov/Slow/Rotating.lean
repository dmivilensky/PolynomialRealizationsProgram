import nesterov.Slow.Sampled
import nesterov.Spectral.AtomicCoordinates
import nesterov.Spectral.Rotation

/-! Literal Euclidean self-similar trajectories for the fixed sampled flow spectrum. -/
namespace nesterov.Slow
noncomputable section
open Spectral Filter Flow Set
open scoped Topology NNReal

 theorem finite_rotating_real_objective {J : Type*} [Fintype J] [DecidableEq J]
    (M : StationaryMethod) {μ L t C : ℝ} (hμ : 0<μ) (hμL : μ<L)
    (v : J→ℝ≥0) (f : J→Frequency) (hv : ∑ j,v j=1)
    (hpos : ∀ j,0<v j) (hinj : Function.Injective f)
    (h : Feasible (M.symbolPair μ L t) t (finiteSpectrum v f hv) C) :
    ∃ (F : EuclideanSpace ℝ (Fin (2*Fintype.card J))→ℝ)
      (x : ℕ→EuclideanSpace ℝ (Fin (2*Fintype.card J)))
      (U : EuclideanSpace ℝ (Fin (2*Fintype.card J)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2*Fintype.card J))),
      polyak.CenteredSmoothStronglyConvex μ L F ∧ M.IsTrajectory (gradient F) x ∧
      (∀ k,x (k+1)=Real.exp t • U (x k)) ∧
      (∀ k,WithLp.toLp 2 (fun j : Fin M.memory=>x (k+1+j.val))=
        Real.exp t • (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin M.memory=>U))
          (WithLp.toLp 2 (fun j : Fin M.memory=>x (k+j.val)))) ∧
      ∀ k,‖x k‖=Real.exp (k*t) := by
  let ν := finiteSpectrum v f hv
  let e := atomicRealCoordinates v f hv hpos hinj
  obtain ⟨F,hF,ht⟩ := h.exists_objective hμ hμL
  let U := (e.symm.trans (rotation ν)).trans e
  let x := fun k=>e (latent ν t k)
  refine ⟨polyak.extendObjective μ L e.toLinearIsometry F,x,U,
    hF.extendObjective e.toLinearIsometry,?_,?_,?_,?_⟩
  · intro k
    have hq : M.query x k=e (M.query (latent ν t) k) := by
      simp [x,StationaryMethod.query,map_sum,map_smul]
    rw [hq]
    have hg := polyak.gradient_extendObjective_embed hF.toSmoothStronglyConvex e.toLinearIsometry (M.query (latent ν t) k)
    change gradient (polyak.extendObjective μ L e.toLinearIsometry F) (e (M.query (latent ν t) k))=
      e (gradient F (M.query (latent ν t) k)) at hg
    rw [hg]
    simpa only [map_sum,map_smul] using congrArg e (ht k)
  · intro k
    change e (latent ν t (k+1))=Real.exp t • e (rotation ν (e.symm (e (latent ν t k))))
    rw [e.symm_apply_apply,rotation_latent,e.map_smul]
  · intro k
    apply PiLp.ext
    intro j
    change e (latent ν t (k+1+j.val))=Real.exp t • e (rotation ν (e.symm (e (latent ν t (k+j.val)))))
    rw [e.symm_apply_apply,show k+1+j.val=k+j.val+1 by omega,rotation_latent,e.map_smul]
  · intro k
    rw [e.norm_map]
    exact norm_latent ν t k

 theorem spread_frequency_injective {θ y c : ℝ} (W : SpreadWitness θ y c) :
    Function.Injective W.spectrum.frequency := by
  intro i j hij
  rw [W.frequency_eq,W.frequency_eq] at hij
  have hs : W.scale≠0 := (zero_lt_one.trans_le W.scale_ge_one).ne'
  have hJ : (W.J:ℝ)≠0 := (Nat.cast_pos.mpr W.J_pos).ne'
  have he : (i:ℝ)=(j:ℝ) := by
    have hh := mul_left_cancel₀ hs hij
    have hd : ((i:ℝ)+1/2)/(W.J:ℝ)=((j:ℝ)+1/2)/(W.J:ℝ) := by linarith
    have hnum := (div_left_inj' hJ).mp hd
    linarith
  exact Fin.ext (Nat.cast_injective he)

 theorem sampled_flow_rotating {θ y c : ℝ} (F : SecondOrderFamily θ y)
    (W : SpreadWitness θ y c) (hc : 0<c) (hb : 0≤θ-2*c) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∃ (f : EuclideanSpace ℝ (Fin (2*W.J))→ℝ)
        (x : ℕ→EuclideanSpace ℝ (Fin (2*W.J)))
        (U : EuclideanSpace ℝ (Fin (2*W.J)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2*W.J))),
        polyak.CenteredSmoothStronglyConvex (ε^2) 1 f ∧
        (F.method ε).IsTrajectory (gradient f) x ∧
        (∀ k,x (k+1)=Real.exp (-c*ε) • U (x k)) ∧
        (∀ k,WithLp.toLp 2 (fun j : Fin (F.method ε).memory=>x (k+1+j.val))=
          Real.exp (-c*ε) • (LinearIsometryEquiv.piLpCongrRight 2
            (fun _ : Fin (F.method ε).memory=>U))
            (WithLp.toLp 2 (fun j : Fin (F.method ε).memory=>x (k+j.val)))) ∧
        ∀ k,‖x k‖=Real.exp (k*(-c*ε)) := by
  have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  have hangle : ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ j : Fin W.J,ε*W.spectrum.frequency j∈Icc (0:ℝ) Real.pi := by
    apply eventually_all.mpr
    intro j
    have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    have ht : Tendsto (fun ε : ℝ=>ε*W.spectrum.frequency j) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa using he.mul_const (W.spectrum.frequency j)
    filter_upwards [ht.eventually (eventually_lt_nhds Real.pi_pos),self_mem_nhdsWithin] with ε hε heps
    exact ⟨mul_nonneg heps.le (W.spectrum.frequency_nonneg j),hε.le⟩
  filter_upwards [sampled_flow_feasible F W hc hb,hsmall,hangle,self_mem_nhdsWithin] with ε he hε1 hω hε0
  obtain ⟨v,hv,C,hfeas,_,hpos⟩ := he
  have hε : 0<ε := hε0
  have hi : Function.Injective (fun j : Fin W.J=>Phase.frequency (ε*W.spectrum.frequency j)) := by
    intro i j hij
    have hh := congrArg (fun x : Frequency=>Real.arccos x) hij
    rw [Phase.arccos_frequency (hω i),Phase.arccos_frequency (hω j)] at hh
    exact spread_frequency_injective W (mul_left_cancel₀ hε.ne' hh)
  have hm : ε^2<1 := by nlinarith
  have H := finite_rotating_real_objective (F.method ε) (sq_pos_of_pos hε) hm v _ hv hpos hi hfeas
  rw [Fintype.card_fin] at H
  exact H

end
end nesterov.Slow
