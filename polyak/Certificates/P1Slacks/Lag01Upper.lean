import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 1, sign 1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate01Upper : Certificate where
  degree0 := 4
  degree1 := 2
  coefficient := ![
    ![2,4,2],
    ![8,16,8],
    ![12,24,12],
    ![8,16,8],
    ![2,4,(943/512)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row01Upper_00 : Expr := (.add (.literal (2)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked01Upper_00 :
    (certificate01Upper.rowExpression ⟨0,by decide⟩).check row01Upper_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row01Upper_01 : Expr := (.add (.literal (8)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked01Upper_01 :
    (certificate01Upper.rowExpression ⟨1,by decide⟩).check row01Upper_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row01Upper_02 : Expr := (.add (.literal (12)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked01Upper_02 :
    (certificate01Upper.rowExpression ⟨2,by decide⟩).check row01Upper_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row01Upper_03 : Expr := (.add (.literal (8)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked01Upper_03 :
    (certificate01Upper.rowExpression ⟨3,by decide⟩).check row01Upper_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row01Upper_04 : Expr := (.add (.literal (2)) (.mul .y (.add (.literal (0)) (.mul .y (.add (.literal ((-81/512))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked01Upper_04 :
    (certificate01Upper.rowExpression ⟨4,by decide⟩).check row01Upper_04=true := by kernel_decide

def rows01Upper : Fin (certificate01Upper.degree0+1) → Expr := ![row01Upper_00,row01Upper_01,row01Upper_02,row01Upper_03,row01Upper_04]

theorem rowsChecked01Upper : ∀ i, (certificate01Upper.rowExpression i).check (rows01Upper i)=true := by
  intro i
  fin_cases i
  · exact checked01Upper_00
  · exact checked01Upper_01
  · exact checked01Upper_02
  · exact checked01Upper_03
  · exact checked01Upper_04


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity01Upper : slackRowsIdentityCheck 1 (1) certificate01Upper rows01Upper=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted01Upper : certificate01Upper.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive01Upper {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 1 (1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate01Upper rows01Upper rowsChecked01Upper identity01Upper accepted01Upper hz hz1 ha

end polyak.Certificates.P1Slacks
