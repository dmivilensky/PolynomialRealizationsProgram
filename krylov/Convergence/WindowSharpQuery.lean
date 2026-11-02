import krylov.Secant.ModelConvergence

/-!
Article: main_krylov, thm:ss1F, exact leading model-to-query transfer.
Use: preserve a proved leading normalized matrix coefficient through the
actual inverse-model query, deriving its inverse domains and little-o
remainder. Source: continuity of inversion and the exact model-step action.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Secant krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {α : Type*} {l : Filter α} {n : ℕ}

/-- A sharp actual matrix coefficient gives the same actual query
coefficient, amplified only by the genuine uniform inverse-frame bound.
The remainder is proved little-o, and model inverse domains are derived. -/
theorem conditioned_model_sharp_query
    (V X A : α → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (v : α → EuclideanSpace ℝ (Fin (n+1))) (q leading r : α → ℝ)
    {C : ℝ} (hC : 0≤C) (hV : ∀ᶠ z in l,‖(V z)⁻¹‖≤C)
    (hX : Tendsto X l (𝓝 0)) (hA : Tendsto A l (𝓝 1))
    (hleading : leading =O[l] q) (hr : r =o[l] q)
    (hmatrix : ∀ᶠ z in l,‖X z‖≤leading z+r z)
    (hnew : (fun z=>A z-1) =o[l] q) :
    let J := fun z=>1+inverseCongruence (V z) (X z)
    ∃ R : α → ℝ,R =o[l] q ∧∀ᶠ z in l,
      ‖WithLp.toLp 2 (WithLp.ofLp (v z)-(J z)⁻¹*ᵥ(A z*ᵥWithLp.ofLp (v z)))‖≤
        (C^2*leading z+R z)*‖v z‖ := by
  let J := fun z=>1+inverseCongruence (V z) (X z)
  let a := fun z=>C^2*leading z
  let b := fun z=>C^2*r z+‖A z-1‖
  have hconv := conditioned_model_convergence V X A v hC hV hX hA
  have ha : a =O[l] q := hleading.const_mul_left (C^2)
  have hb : b =o[l] q := (hr.const_mul_left (C^2)).add hnew.norm_left
  let R := fun z=>(‖(J z)⁻¹‖-1)*a z+‖(J z)⁻¹‖*b z
  have hR : R =o[l] q := by
    have h₁ := hconv.2.2.2.1.mul_isBigO ha
    have h₂ := (hconv.2.1.norm.isBigO_one ℝ).mul_isLittleO hb
    simpa only [one_mul] using h₁.add h₂
  refine ⟨R,hR,?_⟩
  filter_upwards [hV,hmatrix,hconv.2.2.1] with z hv hm hj
  have hcong : ‖inverseCongruence (V z) (X z)‖≤C^2*(leading z+r z) := by
    apply (inverseCongruence_norm _ _).trans
    exact mul_le_mul ((sq_le_sq₀ (norm_nonneg _) hC).mpr hv) hm (norm_nonneg _) (sq_nonneg _)
  have hJA : ‖J z-A z‖≤a z+b z := by
    have he : J z-A z=inverseCongruence (V z) (X z)-(A z-1) := by dsimp only [J]; abel
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add hcong le_rfl).trans_eq (by dsimp only [a,b]; ring))
  have ho := Matrix.l2_opNorm_mulVec (J z)⁻¹
    (WithLp.toLp 2 ((J z-A z)*ᵥWithLp.ofLp (v z)))
  have hi := Matrix.l2_opNorm_mulVec (J z-A z) (v z)
  rw [model_step_identity (J z) (A z) hj]
  apply (ho.trans (mul_le_mul_of_nonneg_left
    (hi.trans (mul_le_mul_of_nonneg_right hJA (norm_nonneg _))) (norm_nonneg _))).trans_eq
  dsimp only [R,a,b]
  ring

/-- Compare a genuine model directly with radial curvature before taking
norms. This preserves a scalar cancellation of their common current-Hessian
term. The actual inverse domain follows from model convergence. -/
theorem direct_model_sharp_query
    (J A : α → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (v : α → EuclideanSpace ℝ (Fin (n+1))) (q leading r : α → ℝ)
    (hJ : Tendsto J l (𝓝 1)) (hleading : leading =O[l] q) (hr : r =o[l] q)
    (herror : ∀ᶠ z in l,‖J z-A z‖≤leading z+r z) :
    ∃ R : α → ℝ,R =o[l] q ∧∀ᶠ z in l,
      ‖WithLp.toLp 2 (WithLp.ofLp (v z)-(J z)⁻¹*ᵥ(A z*ᵥWithLp.ofLp (v z)))‖≤
        (leading z+R z)*‖v z‖ := by
  have hi : Tendsto (fun z=>(J z)⁻¹) l (𝓝 1) := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse,Units.val_one,Ring.inverse_one,Function.comp_def] using
      (NormedRing.inverse_continuousAt (1:(Matrix (Fin (n+1)) (Fin (n+1)) ℝ)ˣ)).tendsto.comp hJ
  have hu : ∀ᶠ z in l,IsUnit (J z).det :=
    (hJ.eventually (Units.isOpen.mem_nhds isUnit_one)).mono fun z hz=>(Matrix.isUnit_iff_isUnit_det _).mp hz
  have hn : (fun z=>‖(J z)⁻¹‖-1) =o[l] (fun _=>(1:ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    simpa only [norm_one,sub_self] using hi.norm.sub_const 1
  let R := fun z=>(‖(J z)⁻¹‖-1)*leading z+‖(J z)⁻¹‖*r z
  have hR : R =o[l] q := by
    have h₁ := hn.mul_isBigO hleading
    have h₂ := (hi.norm.isBigO_one ℝ).mul_isLittleO hr
    simpa only [one_mul] using h₁.add h₂
  refine ⟨R,hR,?_⟩
  filter_upwards [hu,herror] with z hz he
  have ho := Matrix.l2_opNorm_mulVec (J z)⁻¹
    (WithLp.toLp 2 ((J z-A z)*ᵥWithLp.ofLp (v z)))
  have hi := Matrix.l2_opNorm_mulVec (J z-A z) (v z)
  rw [model_step_identity (J z) (A z) hz]
  apply (ho.trans (mul_le_mul_of_nonneg_left
    (hi.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))) (norm_nonneg _))).trans_eq
  dsimp only [R]
  ring

/-- A proved little-o remainder has a literal multiplicative 1+o(1)
factor, even when the leading scale has zero values. -/
theorem littleo_relative_factor (a r : α → ℝ) (hr : r =o[l] a) :
    ∃ θ : α → ℝ,Tendsto θ l (𝓝 0) ∧∀ᶠ z in l,a z+r z=(1+θ z)*a z := by
  refine ⟨fun z=>r z/a z,hr.tendsto_div_nhds_zero,?_⟩
  filter_upwards [hr.def (by norm_num : (0:ℝ)<1)] with z hz
  by_cases ha : a z=0
  · have hzero : r z=0 := norm_eq_zero.mp (le_antisymm
      (by simpa only [ha,norm_zero,mul_zero] using hz) (norm_nonneg _))
    simp only [ha,hzero,add_zero,mul_zero]
  · rw [add_mul,one_mul,div_mul_cancel₀ _ ha]

end
end krylov.Convergence
