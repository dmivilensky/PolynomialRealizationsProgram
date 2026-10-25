import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 4, sign 1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate04Upper : Certificate where
  degree0 := 6
  degree1 := 3
  coefficient := ![
    ![4,12,12,4],
    ![24,72,72,24],
    ![(231/4),(1413/8),(711/4),(471/8)],
    ![71,(453/2),231,(151/2)],
    ![(93/2),(20367/128),(42543/256),(13551/256)],
    ![15,(3663/64),(7983/128),(2415/128)],
    ![(7/4),(1023/128),(2415/256),(21689/8192)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row04Upper_00 : Expr := (.add (.literal (4)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Upper_00 :
    (certificate04Upper.rowExpression ⟨0,by decide⟩).check row04Upper_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row04Upper_01 : Expr := (.add (.literal (24)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Upper_01 :
    (certificate04Upper.rowExpression ⟨1,by decide⟩).check row04Upper_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row04Upper_02 : Expr := (.add (.literal ((231/4))) (.mul .y (.add (.literal ((27/8))) (.mul .y (.add (.literal ((-9/4))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Upper_02 :
    (certificate04Upper.rowExpression ⟨2,by decide⟩).check row04Upper_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row04Upper_03 : Expr := (.add (.literal (71)) (.mul .y (.add (.literal ((27/2))) (.mul .y (.add (.literal (-9)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Upper_03 :
    (certificate04Upper.rowExpression ⟨3,by decide⟩).check row04Upper_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row04Upper_04 : Expr := (.add (.literal ((93/2))) (.mul .y (.add (.literal ((2511/128))) (.mul .y (.add (.literal ((-3213/256))) (.mul .y (.add (.literal ((-81/128))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Upper_04 :
    (certificate04Upper.rowExpression ⟨4,by decide⟩).check row04Upper_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row04Upper_05 : Expr := (.add (.literal (15)) (.mul .y (.add (.literal ((783/64))) (.mul .y (.add (.literal ((-909/128))) (.mul .y (.add (.literal ((-81/64))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Upper_05 :
    (certificate04Upper.rowExpression ⟨5,by decide⟩).check row04Upper_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row04Upper_06 : Expr := (.add (.literal ((7/4))) (.mul .y (.add (.literal ((351/128))) (.mul .y (.add (.literal ((-333/256))) (.mul .y (.add (.literal ((-4455/8192))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Upper_06 :
    (certificate04Upper.rowExpression ⟨6,by decide⟩).check row04Upper_06=true := by kernel_decide

def rows04Upper : Fin (certificate04Upper.degree0+1) → Expr := ![row04Upper_00,row04Upper_01,row04Upper_02,row04Upper_03,row04Upper_04,row04Upper_05,row04Upper_06]

theorem rowsChecked04Upper : ∀ i, (certificate04Upper.rowExpression i).check (rows04Upper i)=true := by
  intro i
  fin_cases i
  · exact checked04Upper_00
  · exact checked04Upper_01
  · exact checked04Upper_02
  · exact checked04Upper_03
  · exact checked04Upper_04
  · exact checked04Upper_05
  · exact checked04Upper_06


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity04Upper : slackRowsIdentityCheck 4 (1) certificate04Upper rows04Upper=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted04Upper : certificate04Upper.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive04Upper {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 4 (1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate04Upper rows04Upper rowsChecked04Upper identity04Upper accepted04Upper hz hz1 ha

end polyak.Certificates.P1Slacks
