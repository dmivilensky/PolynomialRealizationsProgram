import nesterov.Faithful.Necessary
import nesterov.Attainment.RealQuadratic

/-! Literal R² growing quadratic trajectories for faithful(c). -/
namespace nesterov.Faithful
noncomputable section
open Set Filter
open scoped Topology

theorem growing_planar_quadratic_of_root (M : StationaryMethod) {μ L lam : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hlam : lam∈Icc μ L) {z : ℂ}
    (hz : M.characteristic lam z=0) (hn : 1<‖z‖) :
    ∃ t : ℝ,0<t ∧ ∃ w : ℕ→EuclideanSpace ℝ (Fin 2),
      polyak.CenteredSmoothStronglyConvex μ L
        (fun x : EuclideanSpace ℝ (Fin 2)=>lam/2*‖x‖^2) ∧
      M.IsTrajectory (gradient (fun x : EuclideanSpace ℝ (Fin 2)=>lam/2*‖x‖^2)) w ∧
      ∀ k : ℕ,‖w k‖=Real.exp (k*t) := by
  let e := Attainment.complexRealCoordinates.toLinearIsometry
  let f := fun x : ℂ=>lam/2*‖x‖^2
  let F := fun x : EuclideanSpace ℝ (Fin 2)=>lam/2*‖x‖^2
  have he : Rates.scalarQuadratic μ L lam=f := by
    funext x
    dsimp [Rates.scalarQuadratic,polyak.denormalizeFunction,Rates.normalizedCurvature,f]
    field_simp [ne_of_gt (sub_pos.mpr hμL)]
    ring
  have hf := Rates.scalarQuadratic_centered hμ hμL hlam
  rw [he] at hf
  have ht := (Rates.HilbertRun.ofRoot M hμ hμL hlam z hz).trajectory
  change M.IsTrajectory (gradient (Rates.scalarQuadratic μ L lam)) (fun k=>z^k) at ht
  rw [he] at ht
  have hF : polyak.extendObjective μ L e f=F := by
    funext y
    obtain ⟨x,rfl⟩ := Attainment.complexRealCoordinates.surjective y
    change polyak.extendObjective μ L e f (e x)=F (e x)
    rw [polyak.extendObjective_embed hμL]
    simp only [f,F,e.norm_map]
  have hg (x : ℂ) : gradient F (e x)=e (gradient f x) := by
    rw [←hF]
    exact polyak.gradient_extendObjective_embed hf.toSmoothStronglyConvex e x
  let w := fun k : ℕ=>e (z^k)
  refine ⟨Real.log ‖z‖,Real.log_pos hn,w,?_,?_,?_⟩
  · change polyak.CenteredSmoothStronglyConvex μ L F
    rw [←hF]
    exact hf.extendObjective e
  · intro k
    have hq : M.query w k=e (M.query (fun j=>z^j) k) := by
      change (∑ j : Fin M.memory,M.queryCoeff j • e (z^(k+j.val)))=
        e (∑ j : Fin M.memory,M.queryCoeff j • z^(k+j.val))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact (e.map_smul _ _).symm
    rw [hq,hg]
    simpa only [w,map_sum,map_smul] using congrArg e (ht k)
  · intro k
    change ‖e (z^k)‖=Real.exp (k*Real.log ‖z‖)
    rw [e.norm_map,norm_pow,Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans hn)]

theorem negative_lead_planar {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)
    (hlead : effectiveLead (F.u 0) F.q0 y<0) :
    ∃ lam∈Ioo (0:ℝ) 1,∀ᶠ ε in 𝓝[>] (0:ℝ),∃ t : ℝ,0<t ∧
      ∃ w : ℕ→EuclideanSpace ℝ (Fin 2),
        polyak.CenteredSmoothStronglyConvex (ε^2) 1
          (fun x : EuclideanSpace ℝ (Fin 2)=>lam/2*‖x‖^2) ∧
        (F.method ε).IsTrajectory (gradient (fun x : EuclideanSpace ℝ (Fin 2)=>lam/2*‖x‖^2)) w ∧
        ∀ k : ℕ,‖w k‖=Real.exp (k*t) := by
  obtain ⟨lam,hlam,r,hr,he⟩ := F.negative_lead_quadratic_lower hlead
  have hεsq : Tendsto (fun ε : ℝ=>ε^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [zero_pow (by decide : 2≠0)] using
      hid.pow 2
  refine ⟨lam,hlam,?_⟩
  filter_upwards [he,hεsq.eventually (eventually_lt_nhds hlam.1),self_mem_nhdsWithin] with ε he hμ hε
  obtain ⟨z,hz,hn,_⟩ := he
  exact growing_planar_quadratic_of_root _ (sq_pos_of_pos hε) (hμ.trans hlam.2)
    ⟨hμ.le,hlam.2.le⟩ hz (hr.trans hn)

end
end nesterov.Faithful
