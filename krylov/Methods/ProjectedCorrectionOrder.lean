import krylov.Methods.ProjectedModel
import krylov.LinearAlgebra.CorrectionAsymptotics

/-!
Article: main_krylov, lem:projected-residual, finite repeated RFC orders.
Use: transfer normalized error and inverse estimates to the actually executed
observed-gradient correction tree, at every fixed finite correction count.
Source: the proved exact normalized physical solve and mathlib's asymptotic product calculus.
-/

namespace krylov.Methods
noncomputable section
open Matrix Filter Asymptotics Topology
open scoped Matrix.Norms.L2Operator
variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ} {f : Filter α}

/-- Every fixed number of genuine model corrections raises the actual normalized projected-residual order.
Use: the source O(ω^(c+1)) conclusion follows by taking the incoming order q=1.
Article: main_krylov, lem:projected-residual, repeated fixed-model corrections.
Proof: the proved actual finite-query bound is a power of the normalized error
times the bounded inverse; multiply its asymptotic order by the incoming residual order. -/
theorem repeatedModel_projected_order (s : α → Fin p → E) (H : α → Matrix (Fin p) (Fin p) ℝ)
    (B : α → E →L[ℝ] E) (g : α → E) (ω : α → ℝ) (q c : ℕ)
    (hs : ∀ᶠ x in f, ∀ i, s x i≠0)
    (hH : ∀ᶠ x in f, IsUnit (rescaleModel (H x) (fun i => ‖s x i‖⁻¹)).det)
    (hN : (fun x => correctionCompression (unitWindow (s x)) (B x)-
      rescaleModel (H x) (fun i => ‖s x i‖⁻¹)) =O[f] ω)
    (hi : (fun x => (rescaleModel (H x) (fun i => ‖s x i‖⁻¹))⁻¹) =O[f] (fun _ => (1 : ℝ)))
    (hρ : (fun x => projectedResidual (unitWindow (s x)) (g x)) =O[f] (fun x => ω x^q)) :
    (fun x => projectedResidual (unitWindow (s x))
      (runCorrections (repeatedModelTree (s x) (H x) c (g x)) (B x) (g x)).gradient) =O[f]
        (fun x => ω x^(q+c)) := by
  -- The comparison is made only where the actual normalized solve exists.
  let factor := fun x => ‖correctionCompression (unitWindow (s x)) (B x)-
      rescaleModel (H x) (fun i => ‖s x i‖⁻¹)‖*
        ‖(rescaleModel (H x) (fun i => ‖s x i‖⁻¹))⁻¹‖
  have hf : factor =O[f] ω := by
    simpa only [mul_one] using hN.norm_left.mul hi.norm_left
  have hb : (fun x => projectedResidual (unitWindow (s x))
      (runCorrections (repeatedModelTree (s x) (H x) c (g x)) (B x) (g x)).gradient) =O[f]
        (fun x => factor x^c*‖projectedResidual (unitWindow (s x)) (g x)‖) := by
    apply IsBigO.of_bound 1
    filter_upwards [hH,hs] with x hx hxs
    rw [one_mul, Real.norm_of_nonneg (mul_nonneg (pow_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) c) (norm_nonneg _))]
    exact repeatedModel_projected_bound (s x) (H x) _ (unitWindow_diagonal_unit (s x) hxs) hx
      (B x) (g x) c
  exact hb.trans (((hf.pow c).mul hρ.norm_left).congr_right fun x => by rw [← pow_add, Nat.add_comm c q])

/-- Bounded normalized Gram and inverse models transfer the actual projected-residual order to the actual physical correction.
Use: closes the physical-movement premise in the recorded-pair quadratic-error theorem.
Article: main_krylov, lem:projected-residual, χ=O(ω).
Proof: the proved length-independent actual correction bound dominates its
physical norm by a fixed multiple of the genuine normalized residual norm. -/
theorem modelCorrection_movement_order (s : α → Fin p → E) (H : α → Matrix (Fin p) (Fin p) ℝ)
    (g : α → E) (ω : α → ℝ) (hs : ∀ᶠ x in f, ∀ i, s x i≠0)
    {b M : ℝ} (hb : 0≤b)
    (hgram : ∀ᶠ x in f, ‖crossGram (unitWindow (s x)) (unitWindow (s x))‖≤b)
    (hi : ∀ᶠ x in f, ‖(rescaleModel (H x) (fun i => ‖s x i‖⁻¹))⁻¹‖≤M)
    (hρ : (fun x => projectedResidual (unitWindow (s x)) (g x)) =O[f] ω) :
    (fun x => combine (s x) (modelCoefficients (s x) (H x) (g x))) =O[f] ω := by
  have ht : (fun x => combine (s x) (modelCoefficients (s x) (H x) (g x))) =O[f]
      (fun x => projectedResidual (unitWindow (s x)) (g x)) := by
    apply IsBigO.of_bound (Real.sqrt b*M)
    filter_upwards [hgram,hi,hs] with x hxg hxi hxs
    exact (normalizedCorrection_movement_bound (s x) (H x) _
      (unitWindow_diagonal_unit (s x) hxs) (g x) hb hxg).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxi (Real.sqrt_nonneg _)) (norm_nonneg _))
  exact ht.trans hρ

end
end krylov.Methods
