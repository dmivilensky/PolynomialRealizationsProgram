import krylov.OneGradient.InformedCompression
import krylov.Correction.ReferenceOperator
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), source correlated reference bound.
Use: the original actual CG fresh defect and staircase have the full
known-base informed bound, including the genuine prior diagonal.
Source: the already proved correlated compression inequality, genuine
terminal CG geometry and the exact source operator dictionaries.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.Correction krylov.Envelope krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The exact original reference fresh-defect/staircase coefficient with
its genuine unmeasured prior diagonal obeys the full sharp K_X(c) bound.
Every increment and output budget is retained separately; zero and empty
profiles are included, and no separate pivot triangle loss is incurred.
Use: applies directly to the proved actual informed native output formula.
Article: main_krylov, thm:local(b), original source second-order bound.
Proof: true CG geometry supplies the terminal unit and every old-flag
orthogonality premise of the existing correlated compression theorem.
Cauchy--Schwarz bounds the actual prior diagonal by its real matrix budget.
Distribute the genuine output operator and use the exact source definitions. -/
theorem informed_reference_second_order_bound
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (E : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hE : ∀ l∈range n,(E l).IsSymm) (omega : ℕ → ℝ)
    (homega : ∀ l∈range n,‖E l‖≤omega l)
    (R F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (w c : ℝ)
    (hF : ‖F‖≤w) (hR : ‖R‖≤c) :
    let h := canonicalCGUnitStep base g n
    let f := freshDefect base g E (n+1)
    let q := inner ℝ h (cgOperator (R+∑ l∈range n,E l) h)
    ‖staircaseOperator base g E F (n+1) f+q • cgOperator F h‖≤
      informedConstant (∑ l∈range n,omega l) w c := by
  let h := canonicalCGUnitStep base g n
  have hh : ‖h‖=1 := by
    simpa only [Nat.add_sub_cancel] using terminal_unit_norm base hb g hc.ge (by omega : 0<n+1)
  have hr : |inner ℝ h (cgOperator R h)|≤c := by
    calc
      _ ≤ ‖h‖*‖cgOperator R h‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖h‖*(‖cgOperator R‖*‖h‖) := mul_le_mul_of_nonneg_left ((cgOperator R).le_opNorm h) (norm_nonneg _)
      _ = ‖R‖ := by rw [hh,one_mul,mul_one];exact (Matrix.l2_opNorm_toEuclideanCLM R).symm
      _ ≤ c := hR
  have hbound := informed_compression_bound (range n) (oldFlag base g) (fun l => cgOperator (E l))
    (fun l hl => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr (hE l hl))))
    omega (fun l hl => homega l hl) h
    (fun l hl => unitStep_prefix_oldFlag_orthogonal base hb g hc.ge (by omega) (mem_range.mp hl))
    hh (cgOperator F) w c (inner ℝ h (cgOperator R h)) hF ((norm_nonneg R).trans hR) hr
  let f := freshDefect base g E (n+1)
  let r := inner ℝ h (cgOperator R h)+∑ l∈range n,inner ℝ h (cgOperator (E l) h)
  change ‖(∑ l∈range n,(oldFlag base g l).starProjection
    (cgOperator (E l) ((oldFlag base g l).starProjection f)))+cgOperator F (f+r • h)‖≤_ at hbound
  have hq : inner ℝ h (cgOperator (R+∑ l∈range n,E l) h)=r := by
    simp only [r,cgOperator,map_add,map_sum,_root_.add_apply,_root_.sum_apply,inner_add_right,inner_sum]
  change ‖staircaseOperator base g E F (n+1) f+_ • cgOperator F h‖≤_
  rw [hq,staircaseOperator_apply]
  simpa only [Nat.add_sub_cancel,map_add,map_smul,add_assoc] using hbound

end
end krylov.OneGradient
