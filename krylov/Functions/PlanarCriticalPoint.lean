import krylov.Functions.PlanarFiniteMinimax
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
Article: main_krylov, prop:Fcycle(iii), actual shrinking-family critical point.
Use: locate the genuine stationary point of each indistinguishable cubic,
rather than treating the quadratic reference endpoint as its minimizer.
Source: the classical smooth implicit-function theorem (mathlib) applied to
the actual polynomial gradient, whose spatial derivative at the origin is I.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Filter krylov.Tensor.BinaryCubic
open scoped Topology ContDiff

/-- The actual zero-scale planar cubic gradient has identity derivative at
zero. Article: main_krylov, prop:Fcycle(iii). -/
theorem planarCubicGradient_zero_hasFDerivAt (r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    HasFDerivAt (planarCubicGradient 0 r t) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) 0 := by
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x:=(0 : ℝ × ℝ))
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x:=(0 : ℝ × ℝ))
  have hxx : HasFDerivAt (fun z : ℝ × ℝ=>z.1^2) (0 : (ℝ × ℝ) →L[ℝ] ℝ) 0 := by
    convert! hx.pow 2 using 1; simp
  have hxy : HasFDerivAt (fun z : ℝ × ℝ=>z.1*z.2) (0 : (ℝ × ℝ) →L[ℝ] ℝ) 0 := by
    convert! hx.mul hy using 1; simp
  have hyy : HasFDerivAt (fun z : ℝ × ℝ=>z.2^2) (0 : (ℝ × ℝ) →L[ℝ] ℝ) 0 := by
    convert! hy.pow 2 using 1; simp
  have h₁ := ((hxx.const_mul (t.t0/2)).add (hxy.const_mul t.t1)).add (hyy.const_mul (t.t2/2))
  have h₂ := ((hxx.const_mul (t.t1/2)).add (hxy.const_mul t.t2)).add (hyy.const_mul (t.t3/2))
  have hP : HasFDerivAt (planarValueCoordinateDerivative 0 r t) (0 : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) 0 := by
    convert! h₁.prodMk h₂ using 1
    · ext z <;> simp [planarValueCoordinateDerivative] <;> ring
    · simp only [smul_zero,add_zero]
      apply ContinuousLinearMap.ext
      intro z
      rfl
  have hh := (hasFDerivAt_id (0 : ℝ × ℝ)).add hP
  convert! hh using 1
  · ext z <;> simp [planarCubicGradient]
  · simp only [add_zero]

/-- The genuine full planar gradient is jointly smooth in scale and position.
Article: main_krylov, prop:Fcycle(iii), original polynomial regularity. -/
theorem planarCubicGradient_joint_contDiff (r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    ContDiff ℝ ∞ (fun z : ℝ × (ℝ × ℝ)=>planarCubicGradient z.1 r t z.2) := by
  unfold planarCubicGradient planarValueCoordinateDerivative
  fun_prop

set_option maxHeartbeats 600000 in
/-- Every true planar cubic family has a smooth genuine critical-point branch
through zero. The conclusion uses the actual scalar objective differential.
Article: main_krylov, prop:Fcycle(iii), true moving-minimizer foundation. -/
theorem planarCubic_exists_critical_branch (r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    ∃ ψ : ℝ → ℝ × ℝ, ψ 0=0 ∧ ContDiffAt ℝ ∞ ψ 0 ∧
      ∀ᶠ p in 𝓝 (0 : ℝ), fderiv ℝ (planarCubicObjective p r t) (ψ p)=0 := by
  let F := fun z : ℝ × (ℝ × ℝ)=>planarCubicGradient z.1 r t z.2
  have hc : ContDiffAt ℝ ∞ F (0,0) := (planarCubicGradient_joint_contDiff r t).contDiffAt
  have hdiff : DifferentiableAt ℝ F (0,0) := hc.differentiableAt (by norm_num)
  have hi := hdiff.hasFDerivAt.comp (0 : ℝ × ℝ)
    ((ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).hasFDerivAt (x:=0))
  have hspace : fderiv ℝ F (0,0) ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)=
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    exact hi.unique (planarCubicGradient_zero_hasFDerivAt r t)
  have hinv : (fderiv ℝ F (0,0) ∘L ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)).IsInvertible := by
    rw [hspace]
    exact ⟨ContinuousLinearEquiv.refl ℝ (ℝ × ℝ),rfl⟩
  let ψ := hc.implicitFunction (by norm_num) hinv
  refine ⟨ψ,hc.implicitFunction_apply_self (by norm_num) hinv,
    hc.contDiffAt_implicitFunction (by norm_num) hinv,?_⟩
  have he := hc.eventually_apply_implicitFunction (by norm_num) hinv
  filter_upwards [he] with p hp
  have hz : planarCubicGradient p r t (ψ p)=0 := by
    change planarCubicGradient p r t (ψ p)=planarCubicGradient 0 r t 0 at hp
    simpa [planarCubicGradient,planarValueCoordinateDerivative] using! hp
  have hcoord := planarCubicGradient_actual p r t (ψ p)
  rw [hz] at hcoord
  apply ContinuousLinearMap.ext
  intro v
  rw [planarDifferentialCoordinates_reconstruct,←hcoord]
  simp

/-- The genuine critical point is quadratically close to the observed last
point, with no prescribed critical-point expansion as an assumption.
Article: main_krylov, prop:Fcycle(iii), actual normalization foundation. -/
theorem planarCubic_exists_localized_critical_branch (r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    ∃ ψ : ℝ → ℝ × ℝ, ψ 0=0 ∧ ContDiffAt ℝ ∞ ψ 0 ∧
      ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ p : ℝ, 0<p → p<ε₀ →
        fderiv ℝ (planarCubicObjective p r t) (ψ p)=0 ∧ ‖ψ p-(p,r*p)‖≤C*p^2 := by
  obtain ⟨ψ,hψ,hc,hcritical⟩ := planarCubic_exists_critical_branch r t
  obtain ⟨M,hM,hgrowth⟩ := (hc.differentiableAt (by norm_num)).isBigO_sub.exists_pos
  have hbound : ∀ᶠ p in 𝓝 (0 : ℝ), ‖ψ p‖≤M*|p| := by
    filter_upwards [hgrowth.bound] with p hp
    simpa only [hψ,sub_zero,Real.norm_eq_abs] using hp
  obtain ⟨ep,hep,hnear⟩ := Metric.eventually_nhds_iff.mp (hcritical.and hbound)
  obtain ⟨B,hB,hperturb⟩ := planarValueCoordinateDerivative_scaled_bound r t M
  refine ⟨ψ,hψ,hc,ep,B,hep,hB,?_⟩
  intro p hp he
  have hh := hnear (y:=p) (by simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_pos hp] using he)
  refine ⟨hh.1,?_⟩
  have hnorm : ‖ψ p‖≤M*p := by simpa only [abs_of_pos hp] using hh.2
  have hz : planarCubicGradient p r t (ψ p)=0 := by
    rw [planarCubicGradient_actual,hh.1]
    rfl
  have heq : ψ p-(p,r*p)= -planarValueCoordinateDerivative p r t (ψ p) := by
    have hh' := hz
    unfold planarCubicGradient at hh'
    exact eq_neg_of_add_eq_zero_left hh'
  rw [heq,norm_neg]
  exact hperturb p hp (ψ p) hnorm

end
end krylov.Functions
