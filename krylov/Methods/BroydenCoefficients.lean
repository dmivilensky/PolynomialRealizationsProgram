import krylov.Methods.BroydenModel
import krylov.Methods.ObservationSynthesis

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, genuine primitive convex Broyden coefficients.
Use: execute actual inverse convex Broyden actions in finite scalar observation coordinates, preserving every true physical inner-product denominator.
Source: genuine DFP/BFGS linear-map actions and actual finite observation synthesis; the coordinate recursion implements both real endpoint updates exactly.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

/-- The actual inverse convex Broyden model is executed in genuine finite observed-vector coefficient coordinates.
Use: The actual inverse convex Broyden model is executed in genuine finite observed-vector coefficient coordinates.
Article: main_krylov, def:classes, genuine primitive convex Broyden coefficients.
Proof: Recursively synthesize the true older input and secant-image model actions, compute actual physical pairings and combine the genuine endpoint coefficient vectors. -/
def inverseBroydenCoefficients (data : Fin m → E) (c : ℝ) (θ : ℕ → ℝ) :
    List ((Fin m → ℝ) × (Fin m → ℝ)) → (Fin m → ℝ) → (Fin m → ℝ)
  | [],v => c • v
  | (s,y)::W,v =>
      let f := observationSynthesis data
      let Hv := inverseBroydenCoefficients data c θ W v
      let Hy := inverseBroydenCoefficients data c θ W y
      let ρ := (inner ℝ (f s) (f y))⁻¹
      let σ := inner ℝ (f y) (f Hy)
      let b := inner ℝ (f s) (f v)
      let a := inner ℝ (f y) (f Hv)
      let dfp := Hv-(a/σ) • Hy+(ρ*b) • s
      let bfgs := Hv-(ρ*b) • Hy+
        ((ρ*b)-ρ*(a-(ρ*b)*σ)) • s
      (1-θ W.length) • dfp+θ W.length • bfgs

/-- Synthesizing the genuine convex Broyden coefficients gives exactly the actual physical observed-pair inverse-model action.
Use: Synthesizing the genuine convex Broyden coefficients gives exactly the actual physical observed-pair inverse-model action.
Article: main_krylov, def:classes, genuine primitive convex Broyden coefficients.
Proof: Induct through true observed coefficient pairs, distribute genuine linear synthesis and substitute the proved actual endpoint actions. -/
theorem inverseBroydenCoefficients_synthesis (data : Fin m → E) (c : ℝ) (θ : ℕ → ℝ)
    (W : List ((Fin m → ℝ) × (Fin m → ℝ))) (v : Fin m → ℝ) :
    observationSynthesis data (inverseBroydenCoefficients data c θ W v)=
      inverseBroydenModel c θ (W.map (fun p => (observationSynthesis data p.1,observationSynthesis data p.2)))
        (observationSynthesis data v) := by
  induction W generalizing v with
  | nil => exact map_smul _ _ _
  | cons p W ih =>
    simp only [inverseBroydenCoefficients,List.map_cons,inverseBroydenModel,
      inverseBroydenUpdate,LinearMap.add_apply,LinearMap.smul_apply,
      inverseDFPUpdate_apply,inverseBFGSUpdate_apply,map_add,map_sub,map_smul,ih,List.length_map,
      inner_sub_right,real_inner_smul_right,div_eq_mul_inv]
    module
end
end krylov.Methods
