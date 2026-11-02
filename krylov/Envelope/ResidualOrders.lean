import krylov.LinearAlgebra.EuclideanAsymptotics
import krylov.Methods.ProjectedModel
import Mathlib.Analysis.Calculus.Deriv.Basic

set_option autoImplicit false
/-!
Article: main_krylov, apB:eq:nu and apD:prefix, genuine residual derivative orders.
Use: transfer actual normalized projected-residual estimates to real
recorded-coordinate pairings and derive their genuine vanishing first
derivatives from proved higher-order residual bounds.
Source: true Euclidean finite-coordinate asymptotics, zero-safe actual
normalization and the standard little-o characterization of derivatives.
-/

namespace krylov.Envelope
noncomputable section
open Filter Asymptotics Topology krylov.Methods krylov.LinearAlgebra
variable {E X F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {p : ℕ}

omit [NormedSpace ℝ X] in
/-- Every actual normalized finite-window projected-residual order gives the same true unnormalized observed-coordinate order for continuous genuine columns, including zero columns.
Use: Every actual normalized finite-window projected-residual order gives the same true unnormalized observed-coordinate order for continuous genuine columns, including zero columns.
Article: main_krylov, apB:eq:nu and apD:prefix, genuine residual derivative orders.
Proof: Read the actual Euclidean coordinate order, multiply by the locally bounded true column norm and use its genuine zero-safe norm-times-normalization identity. -/
theorem raw_residual_order (s : X → Fin p → E) (g : X → E) (ω : X → ℝ)
    (hs : ∀ i, ContinuousAt (fun x => s x i) 0)
    (hO : (fun x => projectedResidual (unitWindow (s x)) (g x)) =O[𝓝 (0 : X)] ω) :
    ∀ i, (fun x => inner ℝ (s x i) (g x)) =O[𝓝 (0 : X)] ω := by
  -- Undo true normalization using the exact zero-safe norm identity, without imposing a nonzero-column premise.
  intro i
  have hi := (euclidean_bigO_iff_entry _ _).mp hO i
  have h := ((hs i).norm.tendsto.isBigO_one ℝ).mul hi
  apply (h.congr_right (fun x => one_mul (ω x))).congr_left
  intro x
  change ‖s x i‖*inner ℝ (‖s x i‖⁻¹ • s x i) (g x)=inner ℝ (s x i) (g x)
  rw [← real_inner_smul_left]
  change inner ℝ (‖s x i‖ • NormedSpace.normalize (s x i)) (g x)=_
  rw [NormedSpace.norm_smul_normalize]

/-- Every genuine residual with a proved superlinear norm-power order has true derivative zero at the actual origin.
Use: Every genuine residual with a proved superlinear norm-power order has true derivative zero at the actual origin.
Article: main_krylov, apB:eq:nu and apD:prefix, genuine residual derivative orders.
Proof: The real big-O estimate forces its actual reference value to zero; the standard norm-power little-o identity supplies the genuine zero derivative criterion. -/
theorem hasDerivAt_zero_of_norm_order (f : ℝ → F) (q : ℕ) (hq : 1<q)
    (hO : f =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^q)) : HasDerivAt f 0 0 := by
  have h0 : f 0=0 := by
    have h : f =O[𝓝 (0 : ℝ)] (fun t => ‖t-0‖^q) := by simpa only [sub_zero] using hO
    exact h.eq_zero_of_norm_pow (by omega)
  apply hasDerivAt_iff_isLittleO.mpr
  simpa only [h0,sub_zero,smul_zero] using hO.trans_isLittleO (isLittleO_norm_pow_id hq)
end
end krylov.Envelope
