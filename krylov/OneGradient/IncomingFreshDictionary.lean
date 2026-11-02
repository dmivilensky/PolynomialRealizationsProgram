import krylov.OneGradient.InformedIncomingVector
import krylov.Correction.TerminalCGResponse
import krylov.Secant.Trajectory
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine incoming fresh-defect dictionary.
Use: identify the actual whole-segment drift vector with the article's
existing fresh defect in the actual canonical physical increments.
Source: finite telescoping, true full orthonormal CG coordinates and the
already proved original fresh-defect coordinate suffix identity.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.Correction krylov.Envelope krylov.Stability krylov.Variation
open scoped BigOperators InnerProductSpace
variable {n : ℕ}

/-- Actual canonical physical increments telescope exactly on every
chronological subinterval, including an empty subinterval.
Use: actual segment differences retain precisely the source increment sum.
Article: main_krylov, thm:local(a), real cumulative canonical drift.
Proof: distribute the two fixed inverse roots and use the standard finite
telescoping sum in the additive matrix group. -/
theorem canonicalIncrement_sum_Ico (base : Matrix (Fin n) (Fin n) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (i j : ℕ) (hij : i≤j) :
    (∑ l∈Ico i j,canonicalIncrement base A l)=relativeOperator base (A j-A i) := by
  simp only [canonicalIncrement,relativeOperator]
  rw [← Matrix.sum_mul,← Matrix.mul_sum,Finset.sum_Ico_sub A hij]

/-- The genuine incoming drift computed from the actual native row
equations is exactly the already formalized source fresh defect.
Use: the original known-base formula reuses the same fresh defect and
all its existing compression estimates and sharpness constructions.
Article: main_krylov, thm:local(a), exact actual fhat dictionary.
Proof: pair both real vectors with every actual CG step. Complete genuine
orthonormal coordinates give the computed whole-segment coefficient;
the true source fresh coordinate is its exactly telescoping increment sum. -/
theorem informed_incoming_eq_freshDefect
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (A : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    informedIncomingDrift base g (fun j => cgOperator (A j))=
      freshDefect base g (canonicalIncrement base A) (n+1) := by
  let q := fun i : Fin (n+1) => canonicalCGUnitStep base g i.val
  let R := cgOperator (metricRoot base)⁻¹
  have ho : Orthonormal ℝ q := canonicalCG_frame_of_full_atoms base hb g hc
  apply canonical_step_inner_ext base hb g hc
  intro i hi
  have hcoord : inner ℝ (canonicalCGUnitStep base g i)
      (informedIncomingDrift base g (fun j => cgOperator (A j)))=
        inner ℝ (canonicalCGUnitStep base g i)
          ((R*(cgOperator (A n)-cgOperator (A i))*R) (canonicalCGUnitStep base g n)) :=
    ho.inner_right_fintype (fun j => inner ℝ (q j)
      ((R*(cgOperator (A n)-cgOperator (A j.val))*R) (q (Fin.last n)))) ⟨i,hi⟩
  rw [freshDefect_step_coordinate base hb g hc.ge _ i hi]
  simp only [Nat.add_sub_cancel]
  have hsum := canonicalIncrement_sum_Ico base A i n (by omega)
  have hopsum : (∑ l∈Ico i n,cgOperator (canonicalIncrement base A l))=
      cgOperator (relativeOperator base (A n-A i)) := by
    simpa only [cgOperator,map_sum] using congrArg cgOperator hsum
  rw [← inner_sum,← _root_.sum_apply,hopsum]
  rw [show canonicalCGStep base g i=‖canonicalCGStep base g i‖ • canonicalCGUnitStep base g i
    from (NormedSpace.norm_smul_normalize _).symm,real_inner_smul_left,hcoord,
      real_inner_smul_left]
  simp only [R,relativeOperator,cgOperator,map_mul,map_sub]

end
end krylov.OneGradient
