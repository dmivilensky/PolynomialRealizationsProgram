import krylov.Convergence.WindowModelBounds

/-!
Article: main_krylov, apG:mss, thm:Ip and thm:ss1F.
Use: transfer proved errors of actual observed matrices through genuine
varying full windows. Source-specific leaves derive the error limit from
actual function derivatives before invoking this algebraic transfer.
Source: exact inverse congruence, uniform genuine inverse-coordinate bound,
and continuity/openness of inversion at the identity.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {α : Type*} {l : Filter α}

/-- Actual square observed matrices with proved vanishing normalized data
errors have actual model and inverse limits. This lemma merely transports
the source error; the actual matrix and its inverse are the conclusions. -/
theorem square_window_model_tendsto
    (V H : α → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    {C : ℝ} (hC : 0≤C) (hunit : ∀ᶠ z in l,IsUnit (V z).det)
    (hV : ∀ᶠ z in l,‖(V z)⁻¹‖≤C)
    (herr : Tendsto (fun z=>H z-(V z)ᵀ*V z) l (𝓝 0)) :
    Tendsto (fun z=>inverseCongruence (V z) (H z)) l (𝓝 1) ∧
    Tendsto (fun z=>(inverseCongruence (V z) (H z))⁻¹) l (𝓝 1) ∧
    (∀ᶠ z in l,IsUnit (inverseCongruence (V z) (H z)).det) := by
  let X := fun z=>H z-(V z)ᵀ*V z
  have hh := conditioned_model_convergence V X (fun _=>1) (fun _=>0) hC hV herr tendsto_const_nhds
  have he : (fun z=>1+inverseCongruence (V z) (X z)) =ᶠ[l]
      (fun z=>inverseCongruence (V z) (H z)) := by
    filter_upwards [hunit] with z hz
    simp only [X,inverseCongruence,Matrix.mul_sub,Matrix.sub_mul]
    change 1+(inverseCongruence (V z) (H z)-inverseCongruence (V z) ((V z)ᵀ*V z))=_
    rw [inverseCongruence_gram _ hz]
    abel
  refine ⟨hh.1.congr' he,hh.2.1.congr' (he.mono fun _ h=>congrArg Inv.inv h),?_⟩
  filter_upwards [hh.2.2.1,he] with z hz hez
  rw [←hez]
  exact hz

end
end krylov.Convergence
