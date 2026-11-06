import nesterov.TwoStep.Lower
import nesterov.TwoStep.AsymptoticsQuadraticRest

/-! Theorem B(a): one fixed objective and one fixed from-rest start work
simultaneously at all horizons, in a dimension chosen before ε. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set Flow
open scoped Topology

def scalarThree : ℝ→ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun t := PiLp.single 2 0 t
  map_add' a b := by
    apply PiLp.ext
    intro i
    by_cases hi : i=0 <;> simp [hi]
  map_smul' a b := by
    apply PiLp.ext
    intro i
    by_cases hi : i=0 <;> simp [hi]
  norm_map' a := by simp

namespace Scaling
variable {θ y τ : ℝ} (F : Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ)

 theorem quadratic_rest_witness (he : F.epsilon=id)
    (hbranch : cQ θ y≤θ/3) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∃ (f : EuclideanSpace ℝ (Fin 3)→ℝ) (x₀ : EuclideanSpace ℝ (Fin 3)),
        polyak.CenteredSmoothStronglyConvex (ε^2) 1 f ∧ x₀≠0 ∧
        ∃ c₀ : ℝ,0<c₀ ∧ ∀ N : ℕ,c₀*Real.exp (-((cF θ y+δ)*ε)*N)*‖x₀‖≤
          ‖Momentum.iterate (gradient f) (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize x₀ N‖ := by
  have hquad := F.quadratic_branch_rest_lower hbranch hδ
  rw [he] at hquad
  have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε<1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [hquad,hsmall,self_mem_nhdsWithin] with ε hε hε1 hε0
  have hp : 0<ε := hε0
  have hμL : ε^2<1 := by nlinarith
  let f : ℝ→ℝ := fun x=>ε^2/2*‖x‖^2
  have hf : polyak.CenteredSmoothStronglyConvex (ε^2) 1 f :=
    Momentum.real_quadratic_centered (sq_pos_of_pos hp) hμL ⟨le_rfl,hμL.le⟩
  let F₀ := polyak.extendObjective (ε^2) 1 scalarThree f
  have hF := hf.extendObjective scalarThree
  have hg : ∀ x,gradient F₀ (scalarThree x)=scalarThree (gradient f x) :=
    polyak.gradient_extendObjective_embed hf.toSmoothStronglyConvex scalarThree
  have hx : scalarThree (1:ℝ)≠0 := by
    intro h
    exact one_ne_zero (scalarThree.injective (h.trans scalarThree.map_zero.symm))
  refine ⟨F₀,scalarThree 1,hF,hx,1,zero_lt_one,fun N=>?_⟩
  rw [Momentum.iterate_embedding scalarThree _ _ hg,scalarThree.norm_map,scalarThree.norm_map]
  have hgrad : gradient f=(fun x : ℝ=>ε^2*x) := funext (Momentum.real_quadratic_gradient (ε^2))
  rw [hgrad]
  simpa only [cF,min_eq_right hbranch,id_eq,Real.norm_eq_abs,abs_one,mul_one,one_mul,neg_mul] using hε N

 theorem lower_rest_witness (he : F.epsilon=id)
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ J : ℕ,0<J ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∃ (f : EuclideanSpace ℝ (Fin (2*J+1))→ℝ)
        (x₀ : EuclideanSpace ℝ (Fin (2*J+1))),
        polyak.CenteredSmoothStronglyConvex (ε^2) 1 f ∧ x₀≠0 ∧
        ∃ c₀ : ℝ,0<c₀ ∧ ∀ N : ℕ,c₀*Real.exp (-((cF θ y+δ)*ε)*N)*‖x₀‖≤
          ‖Momentum.iterate (gradient f) (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize x₀ N‖ := by
  by_cases hbranch : cQ θ y≤θ/3
  · exact ⟨1,by norm_num,F.quadratic_rest_witness he hbranch hδ⟩
  · have hgap : θ/3<cQ θ y := lt_of_not_ge hbranch
    obtain ⟨c,hc,hcm⟩ := exists_between (lt_min (by linarith : θ/3<θ/3+δ) hgap)
    have hca : c<θ/3+δ := hcm.trans_le (min_le_left _ _)
    have hcQ : c<cQ θ y := hcm.trans_le (min_le_right _ _)
    obtain ⟨J,hJ,hw⟩ := F.sampled_rest_witness he hs hc hcQ
    refine ⟨J,hJ,?_⟩
    filter_upwards [hw,self_mem_nhdsWithin] with ε hε heps
    obtain ⟨f,x₀,hf,hx,c₀,hc₀,hbound⟩ := hε
    refine ⟨f,x₀,hf,hx,c₀,hc₀,fun N=>?_⟩
    have hcf : cF θ y=θ/3 := min_eq_left hgap.le
    have hexp : Real.exp (-((cF θ y+δ)*ε)*N)≤Real.exp (-(c*ε)*N) := by
      apply Real.exp_le_exp.mpr
      rw [hcf]
      nlinarith [mul_nonneg (show 0≤θ/3+δ-c by linarith) (mul_nonneg heps.le (Nat.cast_nonneg N))]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hc₀.le) (norm_nonneg x₀)).trans (hbound N)

end Scaling

/-- The source dimension J(θ,y,δ) is chosen before the family and its limit τ. -/
 theorem common_lower_dimension {θ y δ : ℝ} (hθ : 0<θ) (hy : 0<y) (hδ : 0<δ) :
    ∃ J : ℕ,0<J ∧ ∀ τ : ℝ,∀ F : Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ,
      F.epsilon=id → (∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1) →
      ∀ᶠ ε in 𝓝[>] (0:ℝ),
        ∃ (f : EuclideanSpace ℝ (Fin (2*J+1))→ℝ)
          (x₀ : EuclideanSpace ℝ (Fin (2*J+1))),
          polyak.CenteredSmoothStronglyConvex (ε^2) 1 f ∧ x₀≠0 ∧
          ∃ c₀ : ℝ,0<c₀ ∧ ∀ N : ℕ,c₀*Real.exp (-((cF θ y+δ)*ε)*N)*‖x₀‖≤
            ‖Momentum.iterate (gradient f) (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize x₀ N‖ := by
  by_cases hbranch : cQ θ y≤θ/3
  · exact ⟨1,by norm_num,fun τ F he _=>F.quadratic_rest_witness he hbranch hδ⟩
  · have hgap : θ/3<cQ θ y := lt_of_not_ge hbranch
    obtain ⟨c,hc,hcm⟩ := exists_between (lt_min (by linarith : θ/3<θ/3+δ) hgap)
    have hca : c<θ/3+δ := hcm.trans_le (min_le_left _ _)
    have hcQ : c<cQ θ y := hcm.trans_le (min_le_right _ _)
    obtain ⟨W⟩ := exists_spread hθ hy hc hcQ
    have hcp : 0<c := by linarith
    have hb : 0≤θ-2*c := by linarith [(lt_cQ_iff θ y c).mp hcQ |>.1]
    refine ⟨W.J,W.J_pos,fun τ F he hs=>?_⟩
    filter_upwards [F.sampled_rest_witness_of_spread he hs W hcp hb,self_mem_nhdsWithin]
      with ε hε heps
    obtain ⟨f,x₀,hf,hx,c₀,hc₀,hbound⟩ := hε
    refine ⟨f,x₀,hf,hx,c₀,hc₀,fun N=>?_⟩
    have hcf : cF θ y=θ/3 := min_eq_left hgap.le
    have hexp : Real.exp (-((cF θ y+δ)*ε)*N)≤Real.exp (-(c*ε)*N) := by
      apply Real.exp_le_exp.mpr
      rw [hcf]
      nlinarith [mul_nonneg (show 0≤θ/3+δ-c by linarith) (mul_nonneg heps.le (Nat.cast_nonneg N))]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hc₀.le) (norm_nonneg x₀)).trans (hbound N)

end
end nesterov.TwoStep
