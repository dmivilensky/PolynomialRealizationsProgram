import krylov.XR.SkewCongruence
import krylov.XR.LocalRelative
import krylov.XR.MetricRigidity
import krylov.Secant.RelativeMetric

/-!
Article: main_krylov, prop:status, transfer to the observed model metric.
Use: derive positive model and exact 1/(1-a) amplification from a genuine
base-metric model-error bound. Source: coercivity and invertible congruence;
both symmetric model errors and skew observed defects are included.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {p : ℕ}

/-- Fixed positive-root congruence preserves subtraction exactly.
Article: main_krylov, prop:status. -/
theorem relativeOperator_sub (G A B : Matrix (Fin p) (Fin p) ℝ) :
    relativeOperator G (A-B)=relativeOperator G A-relativeOperator G B := by
  simp only [relativeOperator,Matrix.mul_sub,Matrix.sub_mul]

/-- A true base-metric model error below one forces positivity of the
observed model and the sharp reciprocal-gap inverse estimate.
Article: main_krylov, prop:status. -/
theorem model_metric_gap (G T : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef) (hT : T.IsSymm)
    (a : ℝ) (ha : a<1) (hgap : relativeBudget G (G-T)≤a) :
    T.PosDef ∧ ‖(relativeOperator G T)⁻¹‖≤(1-a)⁻¹ := by
  let K := relativeOperator G T
  let Z := relativeOperator G (G-T)
  have hs : K.IsSymm := relativeOperator_isSymm G T hT
  have he : K+Z=1 := by
    dsimp only [K,Z]
    rw [relativeOperator_sub,relativeOperator_base G hG]
    abel
  have hcoerc (w : Fin p → ℝ) : (1-a)*‖WithLp.toLp 2 w‖^2≤w ⬝ᵥ (K*ᵥ w) := by
    have hn := coefficient_quadratic_norm_bound Z w
    have hb : ‖Z‖≤a := hgap
    have hq := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖WithLp.toLp 2 w‖)
    have hf := congrArg (fun A : Matrix (Fin p) (Fin p) ℝ=>w ⬝ᵥ (A*ᵥ w)) he
    rw [add_mulVec,dotProduct_add,one_mulVec,real_dot_self] at hf
    have hl := (abs_le.mp hn).2
    nlinarith
  have hpos : 0<1-a := sub_pos.mpr ha
  have hi := coefficient_inverse_of_coercivity K (1-a) hpos hcoerc
  have hK : K.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr hs)
    intro w hw
    have hn : 0<‖WithLp.toLp 2 w‖ := norm_pos_iff.mpr (fun hz=>hw (by simpa using hz))
    have hh := mul_pos hpos (sq_pos_of_pos hn)
    simpa only [star_trivial] using hh.trans_le (hcoerc w)
  have hr := hK.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit ((isUnit_iff_isUnit_det _).mpr (metricRoot_det_unit G hG)))
  have hp : T.PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial,(metricRoot_isSymm G).eq,K,
      relativeOperator_reconstruct G T hG] using hr
  exact ⟨hp,hi.2⟩

/-- The actual relative error transfers to the model metric with the
sharp reciprocal-gap loss. Article: main_krylov, prop:status. -/
theorem relativeBudget_model_transfer (G T E : Matrix (Fin p) (Fin p) ℝ)
    (hG : G.PosDef) (hT : T.IsSymm) (hE : E.IsSymm ∨ Eᵀ= -E)
    (a b : ℝ) (ha : a<1)
    (hgap : relativeBudget G (G-T)≤a) (herror : relativeBudget G E≤b) :
    T.PosDef ∧ relativeBudget T E≤b/(1-a) := by
  have hm := model_metric_gap G T hG hT a ha hgap
  let C := (metricRoot G)⁻¹
  have hC : IsUnit C.det := by
    exact (isUnit_iff_isUnit_det _).mp
      (Matrix.isUnit_nonsing_inv_iff.mpr ((isUnit_iff_isUnit_det _).mpr (metricRoot_det_unit G hG)))
  have hs : Cᵀ=C := by dsimp only [C]; rw [transpose_nonsing_inv,(metricRoot_isSymm G).eq]
  have heq : relativeBudget (relativeOperator G T) (relativeOperator G E)=relativeBudget T E := by
    rcases hE with hsym|hskew
    · simpa only [relativeOperator,C,hs] using relativeBudget_congruence T E C hm.1 hsym hC
    · simpa only [relativeOperator,C,hs] using relativeBudget_skew_congruence T E C hm.1 hskew hC
  have hK := relativeOperator_posDef G T hG hm.1
  refine ⟨hm.1,?_⟩
  rw [←heq]
  calc
    _ ≤ ‖(relativeOperator G T)⁻¹‖*‖relativeOperator G E‖ :=
      relativeBudget_le_inverse_norm _ _ hK
    _ ≤ (1-a)⁻¹*b := mul_le_mul hm.2 herror (norm_nonneg _) (inv_nonneg.mpr (sub_pos.mpr ha).le)
    _ = _ := by ring

end
end krylov.XR
