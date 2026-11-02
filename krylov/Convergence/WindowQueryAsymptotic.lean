import krylov.Secant.ModelConvergence

/-!
Article: Lemma A.8 [apG:mss] of krylov.tex.
Use: propagate a proved little-o normalized matrix error to the genuine
inverse-model query at the corresponding product scale. Neither the model
inverse domain nor the desired query asymptotics are assumed.
Source: continuity of inversion at the identity and the exact model-step
identity, followed by the bounded matrix/vector action.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Secant krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {α : Type*} {l : Filter α} {n : ℕ}

/-- A vanishing normalized source remainder gives the actual query's
little-o product scale. All inverse domains are obtained from convergence. -/
theorem conditioned_model_query_littleo_product
    (V X A : α → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (v : α → EuclideanSpace ℝ (Fin (n+1))) (q : α → ℝ) {C : ℝ} (hC : 0≤C)
    (hV : ∀ᶠ z in l,‖(V z)⁻¹‖≤C) (hq : Tendsto q l (𝓝 0))
    (hX : X =o[l] q) (hA : (fun z=>A z-1) =o[l] q) :
    let J := fun z=>1+inverseCongruence (V z) (X z)
    (fun z=>WithLp.toLp 2 (WithLp.ofLp (v z)-(J z)⁻¹*ᵥ(A z*ᵥWithLp.ofLp (v z)))) =o[l]
      (fun z=>q z*‖v z‖) := by
  dsimp only
  let J := fun z=>1+inverseCongruence (V z) (X z)
  have hXt : Tendsto X l (𝓝 0) := hX.trans_tendsto hq
  have hAt : Tendsto A l (𝓝 1) := tendsto_iff_norm_sub_tendsto_zero.mpr
    (hA.norm_left.trans_tendsto hq)
  have hconv := conditioned_model_convergence V X A v hC hV hXt hAt
  have hJ : (fun z=>J z-1) =o[l] q := by
    simpa only [J,add_sub_cancel_left] using
      (varying_congruence_bigO V X hC hV).trans_isLittleO hX
  have hJA : (fun z=>J z-A z) =o[l] q := by
    simpa only [sub_sub_sub_cancel_right] using hJ.sub hA
  have hT : (fun z=>(J z)⁻¹*(J z-A z)) =o[l] q := by
    simpa only [one_mul] using (hconv.2.1.isBigO_one ℝ).mul_isLittleO hJA
  have hv := matrix_vector_littleO _ v q hT
  apply hv.congr' _ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hconv.2.2.1] with z hz
  rw [model_step_identity (J z) (A z) hz,mulVec_mulVec]

end
end krylov.Convergence
