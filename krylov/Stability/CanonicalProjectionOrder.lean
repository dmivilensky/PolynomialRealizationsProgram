import krylov.Methods.CanonicalWindows
import krylov.LinearAlgebra.EuclideanAsymptotics

/-!
Article: main_krylov, lem:projected-residual, canonical normalized actual residual orders.
Use: physical local projected-residual orders pass to the genuine positive-root
canonical unit columns and dual gradients, without a minimum physical step length.
Source: the proved actual primal/dual pairing, nonsingular root cancellation,
and finite Euclidean coordinate asymptotic calculus.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.LinearAlgebra
open scoped Topology InnerProductSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {n p : ℕ}

omit [NormedSpace ℝ X] in
/-- Every actual normalized physical projected-residual order is preserved in the genuine canonical metric near nonzero reference columns.
Use: source RFC order conclusions concern actual canonical unit steps and the true dual output gradient.
Article: main_krylov, lem:projected-residual, physical-to-canonical prefix order.
Proof: true primal/dual metric pairings agree. Each normalized canonical
coordinate is the true normalized physical coordinate times the actual ratio
of physical and canonical column norms; genuine nonzero reference columns and
the real invertible root make these ratios locally bounded. -/
theorem canonical_projectedResidual_order (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s : X → Fin p → EuclideanSpace ℝ (Fin n)) (g : X → EuclideanSpace ℝ (Fin n)) (q : ℕ)
    (hs : ∀ i, ContinuousAt (fun z => s z i) 0) (hn : ∀ i, s 0 i≠0)
    (hρ : (fun z => projectedResidual (unitWindow (s z)) (g z)) =O[𝓝 (0 : X)] (fun z => ‖z‖^q)) :
    (fun z => projectedResidual (unitWindow (primalWindow base (s z)))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (g z))) =O[𝓝 (0 : X)] (fun z => ‖z‖^q) := by
  -- The coordinate factors are actual norm ratios; only their genuine reference nonzero values enter local boundedness.
  have hsn : ∀ᶠ z in 𝓝 (0 : X), ∀ i, s z i≠0 :=
    Filter.eventually_all.mpr fun i => (hs i).eventually_ne (hn i)
  have hroot (i : Fin p) : primalWindow base (s 0) i≠0 := by
    intro hz
    have he := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹) hz
    simp only [map_zero] at he
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (s 0 i))=0 at he
    rw [canonical_primal_dual_cancel base hb] at he
    exact hn i he
  apply (euclidean_bigO_iff_entry _ _).mpr
  intro i
  have hc : ContinuousAt (fun z => primalWindow base (s z) i) 0 :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)).continuous.continuousAt.comp (hs i)
  have hr := ((hs i).norm.mul (hc.norm.inv₀ (norm_ne_zero_iff.mpr (hroot i)))).tendsto.isBigO_one ℝ
  have ht := hr.mul ((euclidean_bigO_iff_entry _ _).mp hρ i)
  apply (ht.congr_right (fun z => one_mul (‖z‖^q))).congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hsn] with z hzs
  change (‖s z i‖*‖primalWindow base (s z) i‖⁻¹)*inner ℝ (‖s z i‖⁻¹ • s z i) (g z)=
    inner ℝ (‖primalWindow base (s z) i‖⁻¹ • primalWindow base (s z) i)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (g z))
  rw [real_inner_smul_left,real_inner_smul_left]
  have hp : inner ℝ (primalWindow base (s z) i)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (g z)) = inner ℝ (s z i) (g z) :=
    (canonical_search_pairing base hb (s z i) (g z)).symm
  rw [hp]
  calc
    _ = ‖primalWindow base (s z) i‖⁻¹*(‖s z i‖*‖s z i‖⁻¹)*inner ℝ (s z i) (g z) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hzs i)),mul_one]

end
end krylov.Stability
