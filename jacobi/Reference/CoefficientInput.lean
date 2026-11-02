import jacobi.Reference.IntegralNorm

/-!
Article: jacobi, Theorem 2.1.
For a fixed continuous complex spatial function, the original source
coefficient integral is a bounded real-linear functional of its genuine
L2 input. This is the same actual integral used in the entire coefficient
transform. Its continuity transfers the proved L2 continuity of k_t
to spatial continuity of the transformed solution.
Use: makes the genuine GL integral continuous along the already constructed L2 row curve, proving spatial continuity of u and its spectral profiles.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex MeasureTheory Filter
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual source coefficient integral as a bounded real-linear functional of its original L2 input.
Use: makes the genuine GL integral continuous along the already constructed L2 row curve, proving spatial continuity of u and its spectral profiles.
Article: jacobi, Theorem 2.1.
-/
def coefficientInput (g : C(Interval,ℂ)) : Space →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun v := coefficientFunctional v g
      map_add' := by
        intro v w
        change (∫ r:Interval,((v+w) r:ℂ)*g r)=
          (∫ r:Interval,(v r:ℂ)*g r)+(∫ r:Interval,(w r:ℂ)*g r)
        rw [← integral_add (coefficient_integrable v g) (coefficient_integrable w g)]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add v w] with r hr
        rw [hr]
        change ((v r+w r:ℝ):ℂ)*g r=(v r:ℂ)*g r+(w r:ℂ)*g r
        rw [Complex.ofReal_add,add_mul]
      map_smul' := by
        intro c v
        change (∫ r:Interval,((c • v) r:ℂ)*g r)=
          c • (∫ r:Interval,(v r:ℂ)*g r)
        rw [← integral_smul]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul c v] with r hr
        rw [hr]
        change ((c*v r:ℝ):ℂ)*g r=(c:ℂ)*((v r:ℂ)*g r)
        rw [Complex.ofReal_mul,mul_assoc] }
    ‖g‖ (fun v => by
      change ‖∫ r:Interval,(v r:ℂ)*g r‖≤‖g‖*‖v‖
      exact ((coefficient_integral_bound v g).trans
        (mul_le_mul_of_nonneg_right (space_L1_le_norm v) (norm_nonneg g))).trans_eq (mul_comm _ _))

/-- The actual input-linear source functional is precisely the same original coefficient integral as the earlier wave-linear functional.
Use: spatial continuity and entire energy dependence apply to one identical original GL correction integral, with no replacement transform.
Article: jacobi, Theorem 2.1.
Proof: the input-linear map is defined by this actual original integral functional, so the equality is definitional. -/
theorem coefficientInput_apply (g : C(Interval,ℂ)) (v : Space) :
    coefficientInput g v=coefficientFunctional v g := rfl

end
end jacobi.Reference
