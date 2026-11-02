import krylov.Correction.TerminalFreshCoordinates
import krylov.Correction.TerminalStaircaseComparison
import krylov.Correction.FlagCoordinates
import krylov.Stability.CanonicalResponseCoordinates

/-!
Article: main_krylov, thm:UCq, exact genuine CG terminal coefficient.
Use: Identify the reference value of the quantitative oblique calculation
with the original fresh defect, staircase and actual last CG step scale.
Source: the existing true CG frame, old-flag pairing selection and actual
fresh-defect coordinates; no separately chosen reference basis is introduced.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
  krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every transported flag of the true full CG unit-step matrix is exactly its original orthogonal old-flag projection.
Use: Transfer the quantitative moving-basis response to the original reference geometry.
Article: main_krylov, thm:UCq.
Proof: Genuine CG orthogonality makes its actual transported flag symmetric. Its true column pairings and the existing old-flag coordinate selector agree on the full active CG step basis, which determines the real action uniquely.
-/
theorem canonicalCG_transportedFlag (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n) (l : ℕ) :
    cgOperator (transportedFlag (canonicalCGUnitMatrix base g) l)=(oldFlag base g l).starProjection := by
  let Q := canonicalCGUnitMatrix base g
  have hu := canonicalCGUnitMatrix_unit base hb g hcount
  have hsym : (transportedFlag Q l)ᵀ=transportedFlag Q l := by
    unfold transportedFlag
    rw [show Q⁻¹=Qᵀ from canonicalCGUnitMatrix_inverse base hb g hcount]
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,(prefixProjection_isSymm n l).eq,Matrix.mul_assoc]
  apply ContinuousLinearMap.ext
  intro v
  apply canonical_step_inner_ext base hb g hcount
  intro i hi
  let j : Fin n := ⟨i,hi⟩
  have hs : canonicalCGStep base g i=‖canonicalCGStep base g i‖ • WithLp.toLp 2 (fun a => Q a j) :=
    (NormedSpace.norm_smul_normalize _).symm
  have hrow := column_inner_transportedFlag Q hu l j v
  rw [hsym] at hrow
  change inner ℝ (WithLp.toLp 2 (fun a => Q a j)) (cgOperator (transportedFlag Q l) v)=_ at hrow
  rw [step_inner_oldFlag_prefix base hb g hcount.ge hi]
  calc
    _ = ‖canonicalCGStep base g i‖*inner ℝ (WithLp.toLp 2 (fun a => Q a j)) (cgOperator (transportedFlag Q l) v) := by
      conv_lhs => rw [hs,real_inner_smul_left]
    _ = _ := by
      rw [hrow]
      by_cases hil : i≤l
      · simp only [show j.val=i from rfl,ite_eq_left hil]
        conv_rhs => rw [hs,real_inner_smul_left]
      · simp only [show j.val=i from rfl,ite_eq_right hil,mul_zero]

/-- The oblique staircase evaluated on the genuine CG frame is exactly the original source staircase operator.
Use: Identify the actual leading operator in the uniform terminal expansion.
Article: main_krylov, thm:UCq.
Proof: Each genuine CG transported flag is its true symmetric old orthogonal projection. Apply the exact finite matrix/operator dictionary term by term.
-/
theorem canonicalCG_obliqueStaircase (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ) :
    cgOperator (obliqueStaircase (canonicalCGUnitMatrix base g) E F (n-1))=
      staircaseOperator base g E F n := by
  have hsym l : (transportedFlag (canonicalCGUnitMatrix base g) l)ᵀ=
      transportedFlag (canonicalCGUnitMatrix base g) l := by
    unfold transportedFlag
    rw [canonicalCGUnitMatrix_inverse base hb g hcount]
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,(prefixProjection_isSymm n l).eq,Matrix.mul_assoc]
  unfold obliqueStaircase staircaseOperator
  simp only [hsym,cgOperator,map_add,map_sum,map_mul]
  simp_rw [show ∀ l, Matrix.toEuclideanCLM (𝕜 := ℝ) (transportedFlag (canonicalCGUnitMatrix base g) l)=
      (oldFlag base g l).starProjection from fun l => canonicalCG_transportedFlag base hb g hcount l]
  exact add_comm _ _

/-- The genuine single-last-CG-line oblique response is exactly the actual last-step norm times the original fresh defect.
Use: Recover the original reference scale in the uniform cubic coefficient, including arbitrarily small last energies.
Article: main_krylov, thm:UCq.
Proof: Pair with each true CG step and reuse the exact terminal oblique coordinates and scaled fresh-defect coordinates. Their old suffixes coincide and the real final coordinate is zero. Full active CG step pairings determine the vector.
-/
theorem canonicalCG_terminal_obliqueResponse (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    obliqueResponse (canonicalCGUnitMatrix base g) E (terminalLineSequence n (canonicalCGStep base g (n-1)))=
      ‖canonicalCGStep base g (n-1)‖ • freshDefect base g E n := by
  apply canonical_step_inner_ext base hb g hcount
  intro i hi
  let Q := canonicalCGUnitMatrix base g
  let j : Fin n := ⟨i,hi⟩
  have hs : canonicalCGStep base g i=‖canonicalCGStep base g i‖ • WithLp.toLp 2 (fun a => Q a j) :=
    (NormedSpace.norm_smul_normalize _).symm
  have hrow := terminal_oblique_response_coordinates Q (canonicalCGUnitMatrix_unit base hb g hcount)
    E (canonicalCGStep base g (n-1)) j
  rw [freshDefect_scaled_step_pairing base hb g hcount.ge E hi]
  calc
    _ = ‖canonicalCGStep base g i‖*inner ℝ (WithLp.toLp 2 (fun a => Q a j))
        (obliqueResponse Q E (terminalLineSequence n (canonicalCGStep base g (n-1)))) := by
      conv_lhs => rw [hs,real_inner_smul_left]
    _ = _ := by
      rw [hrow]
      by_cases hil : i<n-1
      · simp only [show j.val=i from rfl,ite_eq_left hil]
        conv_rhs => rw [hs,real_inner_smul_left]
      · have hilast : i=n-1 := by omega
        rw [ite_eq_right (show ¬j.val<n-1 from hil),mul_zero]
        simp only [hilast,Ico_self,sum_empty,
          cgOperator,map_zero,_root_.zero_apply,inner_zero_right]

end
end krylov.Correction
