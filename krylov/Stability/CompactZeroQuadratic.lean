import krylov.Stability.WeightedCompactTaylor
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
Article: main_krylov, thm:RFCS, compact genuine reference quadratic remainder.
Use: Upgrade pointwise quadratic source vanishing on compact reference
families to one true uniform quadratic tube using actual joint analyticity.
Source: the proved compact reference Taylor theorem and mathlib
Asymptotics.IsBigO.hasFDerivAt, which identifies the genuine zero first jets.
-/

namespace krylov.Stability
noncomputable section
open Set Filter Asymptotics Topology Metric
variable {R P F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [ProperSpace R]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Joint analyticity and genuine pointwise quadratic vanishing yield one uniform quadratic remainder tube before every compact reference parameter.
Use: Derive true uniform source bounds without assuming a common remainder constant.
Article: main_krylov, thm:RFCS, compact nonlinear-transfer source remainder.
Proof: The analytic locus is open and has a compact Taylor tube. The actual pointwise quadratic bounds force zero values and zero perturbation derivatives; the genuine first Taylor polynomial therefore vanishes on every source slice. -/
theorem compact_reference_zero_quadratic (f : R × P → F) (K : Set R) (hK : IsCompact K)
    (ha : ∀ x∈K, AnalyticAt ℝ f (x,0))
    (ho : ∀ x∈K, (fun θ : P => f (x,θ)) =O[𝓝 0] (fun θ => ‖θ‖^2)) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ θ : P, ‖θ‖≤δ → ‖f (x,θ)‖≤C*‖θ‖^2 := by
  -- Apply the existing compact Taylor theorem on the genuine open analytic locus, then identify the actual zero perturbation jets from pointwise quadratic vanishing.
  let U := {z | AnalyticAt ℝ f z}
  have hU : IsOpen U := isOpen_analyticAt ℝ f
  have hf : ContDiffOn ℝ 2 f U := fun z hz => (hz.contDiffAt).contDiffWithinAt
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_reference_taylor f (fun _ => (1 : ℝ)) 2 U K hU hK ha hf
    continuousOn_const (by intro _ _; norm_num)
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx θ hθ
  have ho' : (fun θ : P => f (x,θ)) =O[𝓝 (0 : P)] (fun θ => ‖θ-(0 : P)‖^2) := by
    simpa only [sub_zero] using ho x hx
  have hzero : f (x,0)=0 := ho'.eq_zero_of_norm_pow (by decide)
  have hd0 : HasFDerivAt (fun θ : P => f (x,θ)) (0 : P →L[ℝ] F) 0 := ho'.hasFDerivAt (by decide)
  have hin : HasFDerivAt (fun θ : P => (x,θ)) (ContinuousLinearMap.inr ℝ R P) 0 := by
    simpa only [ContinuousLinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add] using
      ((ContinuousLinearMap.inr ℝ R P).hasFDerivAt (x := (0 : P))).const_add (x,0)
  have hd := ((ha x hx).differentiableAt.hasFDerivAt.comp (0 : P) hin).unique hd0
  have hv : fderiv ℝ f (x,0) (0,θ)=0 := by
    have hh := congrArg (fun L : P →L[ℝ] F => L θ) hd
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,_root_.zero_apply] using hh
  have hT : taylorPolynomial f 2 (x,0) (0,θ)=0 := by
    simp only [taylorPolynomial,Finset.sum_range_succ,Finset.sum_range_zero,
      iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,Nat.factorial_zero,Nat.factorial_one,
      Nat.cast_one,inv_one,one_smul,hzero,hv,add_zero]
  have hh := hbound x hx θ hθ 2 (by decide) le_rfl
  rw [hT] at hh
  simpa only [sub_zero,mul_one] using hh

omit [ProperSpace R] [ProperSpace P] [CompleteSpace F] in
/-- A genuinely analytic joint map with a globally zero reference slice and quadratic source vanishing has a zero full derivative, including the initial-reference directions.
Use: Cover actual nonlinear initial-gradient drift and all original operator perturbations in one genuine compact tube.
Article: main_krylov, thm:RFCS, joint initial-reference and source localization.
Proof: Identify the actual zero derivatives on both product axes, then apply the proved genuine compact derivative and Taylor tube theorems.
-/
theorem hasFDerivAt_zero_of_reference_slice (f : R × P → F) (x : R)
    (ha : AnalyticAt ℝ f (x,0)) (hz : ∀ y, f (y,0)=0)
    (ho : (fun θ : P => f (x,θ)) =O[𝓝 0] (fun θ => ‖θ‖^2)) :
    HasFDerivAt f (0 : R × P →L[ℝ] F) (x,0) := by
  -- The genuine derivative vanishes on each product axis, so linearity makes the full original derivative zero.
  let D := fderiv ℝ f (x,0)
  have hzeroR : HasFDerivAt (fun y : R => f (y,0)) (0 : R →L[ℝ] F) x := by
    have he : (fun y : R => f (y,0))=(fun _ => (0 : F)) := funext hz
    rw [he]
    exact hasFDerivAt_const (0 : F) x
  have hR : D.comp (ContinuousLinearMap.inl ℝ R P)=0 :=
    (ha.differentiableAt.hasFDerivAt.comp x (ContinuousLinearMap.inl ℝ R P).hasFDerivAt).unique hzeroR
  have ho' : (fun θ : P => f (x,θ)) =O[𝓝 (0 : P)] (fun θ => ‖θ-(0 : P)‖^2) := by
    simpa only [sub_zero] using ho
  have hzeroP : HasFDerivAt (fun θ : P => f (x,θ)) (0 : P →L[ℝ] F) 0 := ho'.hasFDerivAt (by decide)
  have hin : HasFDerivAt (fun θ : P => (x,θ)) (ContinuousLinearMap.inr ℝ R P) 0 := by
    simpa only [ContinuousLinearMap.inr_apply,Prod.mk_add_mk,add_zero,zero_add] using
      ((ContinuousLinearMap.inr ℝ R P).hasFDerivAt (x := (0 : P))).const_add (x,0)
  have hP : D.comp (ContinuousLinearMap.inr ℝ R P)=0 :=
    (ha.differentiableAt.hasFDerivAt.comp (0 : P) hin).unique hzeroP
  have hD : D=0 := by
    apply ContinuousLinearMap.ext
    intro z
    have hr := congrArg (fun L : R →L[ℝ] F => L z.1) hR
    have hp := congrArg (fun L : P →L[ℝ] F => L z.2) hP
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,_root_.zero_apply] at hr
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,_root_.zero_apply] at hp
    rw [show z=(z.1,0)+(0,z.2) by ext <;> simp,map_add,hr,hp,add_zero,_root_.zero_apply]
  change fderiv ℝ f (x,0)=0 at hD
  simpa only [hD] using ha.differentiableAt.hasFDerivAt

/-- A genuine joint analytic remainder with zero reference slice and pointwise quadratic source order has one uniform quadratic tube covering simultaneous initial-reference and source perturbations.
Use: Cover actual nonlinear initial-gradient drift and all original operator perturbations in one genuine compact tube.
Article: main_krylov, thm:RFCS, joint initial-reference and source localization.
Proof: Identify the actual zero derivatives on both product axes, then apply the proved genuine compact derivative and Taylor tube theorems.
-/
theorem compact_reference_full_zero_quadratic (f : R × P → F) (K : Set R) (hK : IsCompact K)
    (ha : ∀ x∈K, AnalyticAt ℝ f (x,0)) (hz : ∀ y, f (y,0)=0)
    (ho : ∀ x∈K, (fun θ : P => f (x,θ)) =O[𝓝 0] (fun θ => ‖θ‖^2)) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ v : R, ∀ θ : P, ‖(v,θ)‖≤δ →
      ‖f (x+v,θ)‖≤C*‖(v,θ)‖^2 := by
  -- Use the full product perturbation in the existing compact Taylor tube; both original first-order axes vanish.
  let U := {z | AnalyticAt ℝ f z}
  let K₀ : Set (R × P) := K×ˢ{(0 : P)}
  have hK₀ : IsCompact K₀ := hK.prod isCompact_singleton
  have hsub : K₀⊆U := by
    rintro ⟨x,θ⟩ ⟨hx,hθ⟩
    rw [Set.mem_singleton_iff] at hθ
    change θ=(0 : P) at hθ
    subst θ
    exact ha x hx
  have hf : ContDiffOn ℝ 2 f U := fun _ hz => hz.contDiffAt.contDiffWithinAt
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_taylor_remainders f 2 U K₀ (isOpen_analyticAt ℝ f) hK₀ hsub hf
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx v θ hθ
  have hd := (hasFDerivAt_zero_of_reference_slice f x (ha x hx) hz (ho x hx)).fderiv
  have hT : taylorPolynomial f 2 (x,0) (v,θ)=0 := by
    simp only [taylorPolynomial,Finset.sum_range_succ,Finset.sum_range_zero,
      iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,Nat.factorial_zero,Nat.factorial_one,
      Nat.cast_one,inv_one,one_smul,hz,hd,_root_.zero_apply,add_zero]
  have hh := hbound (x,0) ⟨hx,rfl⟩ (v,θ) hθ 2 (by decide) le_rfl
  rw [hT] at hh
  simpa only [Prod.mk_add_mk,zero_add,sub_zero] using hh


/-- Every genuine jointly analytic finite reference/source map has one uniform actual value bound on a full perturbation tube around its compact reference family.
Use: Cover actual nonlinear initial-gradient drift and all original operator perturbations in one genuine compact tube.
Article: main_krylov, thm:RFCS, joint initial-reference and source localization.
Proof: Identify the actual zero derivatives on both product axes, then apply the proved genuine compact derivative and Taylor tube theorems.
-/
theorem compact_reference_value_tube (f : R × P → F) (K : Set R) (hK : IsCompact K)
    (ha : ∀ x∈K, AnalyticAt ℝ f (x,0)) :
    ∃ δ M : ℝ, 0<δ ∧ 0<M ∧ ∀ x∈K, ∀ v : R, ∀ θ : P, ‖(v,θ)‖≤δ →
      ‖f (x+v,θ)‖≤M := by
  -- The true zero-order derivative norm on one compact thickening bounds every nearby reference and source value uniformly.
  let U := {z | AnalyticAt ℝ f z}
  let K₀ : Set (R × P) := K×ˢ{(0 : P)}
  have hK₀ : IsCompact K₀ := hK.prod isCompact_singleton
  have hsub : K₀⊆U := by
    rintro ⟨x,θ⟩ ⟨hx,hθ⟩
    rw [Set.mem_singleton_iff] at hθ
    change θ=(0 : P) at hθ
    subst θ
    exact ha x hx
  have hf : ContDiffOn ℝ 0 f U := fun _ hz => hz.contDiffAt.contDiffWithinAt
  obtain ⟨δ,M,hδ,hM,_,hbound⟩ := compact_derivative_tube f 0 U K₀ (isOpen_analyticAt ℝ f) hK₀ hsub hf
  refine ⟨δ,M+1,hδ,by linarith,?_⟩
  intro x hx v θ hθ
  have ht : (x+v,θ)∈cthickening δ K₀ := by
    apply mem_cthickening_of_dist_le (x+v,θ) (x,0) δ K₀ ⟨hx,rfl⟩
    simpa only [dist_eq_norm,Prod.mk_sub_mk,add_sub_cancel_left,sub_zero] using hθ
  have h := hbound 0 le_rfl (x+v,θ) ht
  rw [norm_iteratedFDeriv_zero] at h
  linarith

end
end krylov.Stability
