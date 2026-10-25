import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 5, sign 1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate05Upper : Certificate where
  degree0 := 8
  degree1 := 4
  coefficient := ![
    ![8,32,48,32,8],
    ![64,256,384,256,64],
    ![(1765/8),(3539/4),1326,(3521/4),(1747/8)],
    ![(1711/4),(3449/2),2580,(3395/2),(1657/4)],
    ![(4075/8),(8285/4),3090,(8015/4),(3805/8)],
    ![(761/2),1567,2328,1477,(671/2)],
    ![(1387/8),(2909/4),(8800395/8192),(1351897/2048),(1147453/8192)],
    ![(175/4),(377/2),(1132683/4096),(166105/1024),(127549/4096)],
    ![(37/8),(83/4),(247947/8192),(34009/2048),(363055/131072)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row05Upper_00 : Expr := (.add (.literal (8)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Upper_00 :
    (certificate05Upper.rowExpression ⟨0,by decide⟩).check row05Upper_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row05Upper_01 : Expr := (.add (.literal (64)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Upper_01 :
    (certificate05Upper.rowExpression ⟨1,by decide⟩).check row05Upper_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row05Upper_02 : Expr := (.add (.literal ((1765/8))) (.mul .y (.add (.literal ((9/4))) (.mul .y (.add (.literal ((-9/2))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Upper_02 :
    (certificate05Upper.rowExpression ⟨2,by decide⟩).check row05Upper_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row05Upper_03 : Expr := (.add (.literal ((1711/4))) (.mul .y (.add (.literal ((27/2))) (.mul .y (.add (.literal (-27)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Upper_03 :
    (certificate05Upper.rowExpression ⟨3,by decide⟩).check row05Upper_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row05Upper_04 : Expr := (.add (.literal ((4075/8))) (.mul .y (.add (.literal ((135/4))) (.mul .y (.add (.literal ((-135/2))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Upper_04 :
    (certificate05Upper.rowExpression ⟨4,by decide⟩).check row05Upper_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row05Upper_05 : Expr := (.add (.literal ((761/2))) (.mul .y (.add (.literal (45)) (.mul .y (.add (.literal (-90)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Upper_05 :
    (certificate05Upper.rowExpression ⟨5,by decide⟩).check row05Upper_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row05Upper_06 : Expr := (.add (.literal ((1387/8))) (.mul .y (.add (.literal ((135/4))) (.mul .y (.add (.literal ((-550773/8192))) (.mul .y (.add (.literal ((-729/4096))) (.mul .y (.add (.literal ((729/2048))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Upper_06 :
    (certificate05Upper.rowExpression ⟨6,by decide⟩).check row05Upper_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row05Upper_07 : Expr := (.add (.literal ((175/4))) (.mul .y (.add (.literal ((27/2))) (.mul .y (.add (.literal ((-108405/4096))) (.mul .y (.add (.literal ((-729/2048))) (.mul .y (.add (.literal ((729/1024))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Upper_07 :
    (certificate05Upper.rowExpression ⟨7,by decide⟩).check row05Upper_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row05Upper_08 : Expr := (.add (.literal ((37/8))) (.mul .y (.add (.literal ((9/4))) (.mul .y (.add (.literal ((-34677/8192))) (.mul .y (.add (.literal ((-729/4096))) (.mul .y (.add (.literal ((40095/131072))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Upper_08 :
    (certificate05Upper.rowExpression ⟨8,by decide⟩).check row05Upper_08=true := by kernel_decide

def rows05Upper : Fin (certificate05Upper.degree0+1) → Expr := ![row05Upper_00,row05Upper_01,row05Upper_02,row05Upper_03,row05Upper_04,row05Upper_05,row05Upper_06,row05Upper_07,row05Upper_08]

theorem rowsChecked05Upper : ∀ i, (certificate05Upper.rowExpression i).check (rows05Upper i)=true := by
  intro i
  fin_cases i
  · exact checked05Upper_00
  · exact checked05Upper_01
  · exact checked05Upper_02
  · exact checked05Upper_03
  · exact checked05Upper_04
  · exact checked05Upper_05
  · exact checked05Upper_06
  · exact checked05Upper_07
  · exact checked05Upper_08


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity05Upper : slackRowsIdentityCheck 5 (1) certificate05Upper rows05Upper=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted05Upper : certificate05Upper.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive05Upper {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 5 (1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate05Upper rows05Upper rowsChecked05Upper identity05Upper accepted05Upper hz hz1 ha

end polyak.Certificates.P1Slacks
