import nesterov.Attainment.Optimal
import polyak.Functions.Embedding

/-! The quadratic alternative in Theorem A(e), on literal real R². -/
noncomputable section
namespace nesterov.Attainment
open scoped BigOperators

def complexRealCoordinates : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := by
  rw [←Complex.finrank_real_complex]
  exact (stdOrthonormalBasis ℝ ℂ).repr

/-- At T=log ρq, one actual quadratic on literal R² attains the exponent
with a nonzero fixed trajectory and the exact complete-state norm at all times. -/
theorem quadratic_optimal_real_attainment (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L)
    (hT : Closure.T M μ L=Real.log (Rates.quadraticRate M μ L)) :
    ∃ lam∈Set.Icc μ L,∃ w : ℕ→EuclideanSpace ℝ (Fin 2),
      polyak.CenteredSmoothStronglyConvex μ L
        (fun x : EuclideanSpace ℝ (Fin 2)=>lam/2*‖x‖^2) ∧
      M.IsTrajectory (gradient (fun x : EuclideanSpace ℝ (Fin 2)=>lam/2*‖x‖^2)) w ∧
      w 0≠0 ∧ (∀ k : ℕ,‖w k‖=Real.exp (k*Closure.T M μ L)) ∧
      (∀ k : ℕ,M.stateNorm w k=Real.exp (k*Closure.T M μ L)*M.stateNorm w 0) := by
  obtain ⟨lam,hlam,z,hf,ht,hn,hs⟩ := quadratic_optimal_attainment M hμ hμL hT
  let e := complexRealCoordinates.toLinearIsometry
  let f := fun x : ℂ=>lam/2*‖x‖^2
  let F := fun x : EuclideanSpace ℝ (Fin 2)=>lam/2*‖x‖^2
  have heq : polyak.extendObjective μ L e f=F := by
    funext y
    obtain ⟨x,rfl⟩ := complexRealCoordinates.surjective y
    change polyak.extendObjective μ L e f (e x)=F (e x)
    rw [polyak.extendObjective_embed hμL]
    simp only [f,F,e.norm_map]
  have hF : polyak.CenteredSmoothStronglyConvex μ L F := by
    rw [←heq]
    exact hf.extendObjective e
  have hg (x : ℂ) : gradient F (e x)=e (gradient f x) := by
    rw [←heq]
    exact polyak.gradient_extendObjective_embed hf.toSmoothStronglyConvex e x
  let w := fun k : ℕ=>e (z^k)
  have hw (k : ℕ) : ‖w k‖=‖z^k‖ := e.norm_map _
  have hstate (k : ℕ) : M.stateNorm w k=M.stateNorm (fun j=>z^j) k := by
    unfold StationaryMethod.stateNorm
    simp only [hw]
  refine ⟨lam,hlam,w,hF,?_,?_,fun k=>(hw k).trans (hn k),?_⟩
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
  · have hn₀ : ‖w 0‖=1 := by rw [hw,hn]; simp
    exact norm_ne_zero_iff.mp (by rw [hn₀]; norm_num)
  · intro k
    rw [hstate,hstate]
    exact hs k
end nesterov.Attainment
