import krylov.Methods.DirectBroydenInverse
import krylov.Methods.BroydenEndpoints
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), actual Dixon BFGS inverse dictionary.
Use: identify the true accumulated two-loop inverse with the inverse of
the literal native zero-parameter direct Broyden model on nonquadratic pairs.
Source: exact direct secant update and the standard two-sided BFGS factors.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual direct BFGS update and the genuine inverse BFGS update
preserve their true inverse action on arbitrary actual observed pairs.
Use: Dixon's real two-loop inverse output is the inverse of the literal
direct recursion even on varying-segment nonquadratic observations.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the genuine backward BFGS factor has zero actual step pairing
after applying the old model. The true direct subtractive term vanishes;
its actual new secant and the genuine forward factor cancel the two
remaining observed-image contributions exactly. -/
theorem directBFGS_inverse_update (B H : E →ₗ[ℝ] E) (s y : E)
    (hBH : ∀ v,B (H v)=v) (ha : inner ℝ s (B s)≠0) (hb : inner ℝ s y≠0) (v : E) :
    directBroydenUpdate B s y 0 (inverseBFGSUpdate H s y v)=v := by
  let a := (inner ℝ s y)⁻¹*inner ℝ s v
  let r := H (v-a • y)
  have hBr : B r=v-a • y := hBH _
  have hsBr : inner ℝ s (B r)=0 := by
    rw [hBr,inner_sub_right,real_inner_smul_right]
    dsimp only [a]
    field_simp
    ring
  calc
    _ = directBroydenUpdate B s y 0 (r+(a-(inner ℝ s y)⁻¹*inner ℝ y r) • s) := by
      rw [inverseBFGSUpdate_apply]
    _ = directBroydenUpdate B s y 0 r+(a-(inner ℝ s y)⁻¹*inner ℝ y r) • y := by
      rw [map_add,map_smul,directBroydenUpdate_secant B s y 0 ha hb]
    _ = v := by
      rw [directBroydenUpdate_apply,hsBr,hBr]
      simp only [zero_smul,sub_zero,zero_mul,add_zero,div_eq_mul_inv]
      module

/-- The actual accumulated two-loop BFGS inverse is a true right inverse
of the literal chronological zero-parameter direct Broyden model on all
positive observed pairs, including nonquadratic varying-segment pairs.
Use: retain Dixon's original implemented output in the perturbation
comparison instead of substituting a latest-information output.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: native chronological positivity gives both real denominators at
all updates. The genuine one-step direct/inverse identity preserves the
true inverse relation through the actual pair recursion; the existing
endpoint dictionary identifies the actual two-loop implementation. -/
theorem directBFGS_model_inverse_action (W : List (E × E))
    (hpair : ∀ p∈W,0 < inner ℝ p.1 p.2) (v : E) :
    directBroydenOperatorModel (ContinuousLinearMap.id ℝ E) (fun _ => 0) W
      (inverseBFGSApply 1 W v)=v := by
  have h (V : List (E × E)) (hp : ∀ p∈V,0 < inner ℝ p.1 p.2) :
      ∀ w,directBroydenOperatorModel (ContinuousLinearMap.id ℝ E) (fun _ => 0) V
        (inverseBroydenModel 1 (fun _ => 1) V w)=w := by
    induction V with
    | nil => intro w; simp only [directBroydenOperatorModel,inverseBroydenModel,LinearMap.id_apply,one_smul,ContinuousLinearMap.id_apply]
    | cons p V ih =>
      have ht : ∀ q∈V,0 < inner ℝ q.1 q.2 := fun q hq => hp q (List.mem_cons_of_mem p hq)
      have hId : (ContinuousLinearMap.id ℝ E).toLinearMap.IsSymmetric := fun _ _ => rfl
      have hpos : ∀ w : E,w≠0 → 0 < inner ℝ w ((ContinuousLinearMap.id ℝ E) w) := by
        intro w hw
        exact real_inner_self_pos.mpr hw
      have hd := directBroydenOperatorModel_pivots (ContinuousLinearMap.id ℝ E) hId hpos
        (fun _ => 0) (fun _ => le_refl 0) (p::V) hp
      intro w
      change directBroydenUpdate (directBroydenOperatorModel (ContinuousLinearMap.id ℝ E) (fun _ => 0) V).toLinearMap
        p.1 p.2 0 (inverseBroydenUpdate (inverseBroydenModel 1 (fun _ => 1) V) p.1 p.2 1 w)=w
      simp only [inverseBroydenUpdate,sub_self,zero_smul,one_smul,zero_add]
      exact directBFGS_inverse_update _ _ _ _ (ih ht) hd.1 hd.2.1 w
  rw [← inverseBroydenModel_bfgs]
  exact h W hpair v

/-- The genuine accumulated two-loop BFGS inverse action equals the
actual inverse physical matrix of the literal direct BFGS recursion on
all positive observed pairs, without a quadratic-data assumption.
Use: the final asymptotic comparison retains the actual Dixon inverse
implementation on its own varying-segment pairs.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the true two-loop inverse is a genuine linear model by the existing
endpoint dictionary. Its proved actual right-inverse relation identifies
its physical matrix with the native matrix inverse by exact multiplication. -/
theorem directBFGS_physical_inverse_action {n : ℕ}
    (W : List (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (hpair : ∀ p∈W,0 < inner ℝ p.1 p.2) (v : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ)
      (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).symm
        (directBroydenOperatorModel (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) (fun _ => 0) W))⁻¹) v=
      inverseBFGSApply 1 W v := by
  let e := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
  let B := directBroydenOperatorModel (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) (fun _ => 0) W
  let H := (inverseBroydenModel 1 (fun _ => 1) W).toContinuousLinearMap
  have hmul : e.symm B*e.symm H=1 := by
    apply e.injective
    have heB : e.toRingEquiv (e.symm B)=B := e.apply_symm_apply B
    have heH : e.toRingEquiv (e.symm H)=H := e.apply_symm_apply H
    rw [map_mul,heB,heH,map_one]
    apply ContinuousLinearMap.ext
    intro w
    change B (H w)=w
    rw [show H w=inverseBFGSApply 1 W w from inverseBroydenModel_bfgs 1 W w]
    exact directBFGS_model_inverse_action W hpair w
  have hi := Matrix.inv_eq_right_inv hmul
  change e ((e.symm B)⁻¹) v=inverseBFGSApply 1 W v
  rw [hi,e.apply_symm_apply]
  exact inverseBroydenModel_bfgs 1 W v

end
end krylov.Methods
