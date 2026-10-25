import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 3, sign -1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate03Lower : Certificate where
  degree0 := 8
  degree1 := 4
  coefficient := ![
    ![8,32,48,32,8],
    ![64,256,384,256,64],
    ![(1765/8),(3521/4),1317,(3503/4),(1747/8)],
    ![(1711/4),(3395/2),2526,(3341/2),(1657/4)],
    ![(4075/8),(8015/4),2955,(7745/4),(3805/8)],
    ![(761/2),1477,2148,1387,(671/2)],
    ![(1387/8),(2639/4),(7694475/8192),(607193/1024),(1147453/8192)],
    ![(175/4),(323/2),(911499/4096),(69593/512),(127549/4096)],
    ![(37/8),(65/4),(174219/8192),(12761/1024),(363055/131072)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row03Lower_00 : Expr := (.add (.literal (8)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked03Lower_00 :
    (certificate03Lower.rowExpression ⟨0,by decide⟩).check row03Lower_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row03Lower_01 : Expr := (.add (.literal (64)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked03Lower_01 :
    (certificate03Lower.rowExpression ⟨1,by decide⟩).check row03Lower_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row03Lower_02 : Expr := (.add (.literal ((1765/8))) (.mul .y (.add (.literal ((-9/4))) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked03Lower_02 :
    (certificate03Lower.rowExpression ⟨2,by decide⟩).check row03Lower_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row03Lower_03 : Expr := (.add (.literal ((1711/4))) (.mul .y (.add (.literal ((-27/2))) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked03Lower_03 :
    (certificate03Lower.rowExpression ⟨3,by decide⟩).check row03Lower_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row03Lower_04 : Expr := (.add (.literal ((4075/8))) (.mul .y (.add (.literal ((-135/4))) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked03Lower_04 :
    (certificate03Lower.rowExpression ⟨4,by decide⟩).check row03Lower_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row03Lower_05 : Expr := (.add (.literal ((761/2))) (.mul .y (.add (.literal (-45)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked03Lower_05 :
    (certificate03Lower.rowExpression ⟨5,by decide⟩).check row03Lower_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row03Lower_06 : Expr := (.add (.literal ((1387/8))) (.mul .y (.add (.literal ((-135/4))) (.mul .y (.add (.literal ((2187/8192))) (.mul .y (.add (.literal ((729/4096))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked03Lower_06 :
    (certificate03Lower.rowExpression ⟨6,by decide⟩).check row03Lower_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row03Lower_07 : Expr := (.add (.literal ((175/4))) (.mul .y (.add (.literal ((-27/2))) (.mul .y (.add (.literal ((2187/4096))) (.mul .y (.add (.literal ((729/2048))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked03Lower_07 :
    (certificate03Lower.rowExpression ⟨7,by decide⟩).check row03Lower_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row03Lower_08 : Expr := (.add (.literal ((37/8))) (.mul .y (.add (.literal ((-9/4))) (.mul .y (.add (.literal ((2187/8192))) (.mul .y (.add (.literal ((729/4096))) (.mul .y (.add (.literal ((-6561/131072))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked03Lower_08 :
    (certificate03Lower.rowExpression ⟨8,by decide⟩).check row03Lower_08=true := by kernel_decide

def rows03Lower : Fin (certificate03Lower.degree0+1) → Expr := ![row03Lower_00,row03Lower_01,row03Lower_02,row03Lower_03,row03Lower_04,row03Lower_05,row03Lower_06,row03Lower_07,row03Lower_08]

theorem rowsChecked03Lower : ∀ i, (certificate03Lower.rowExpression i).check (rows03Lower i)=true := by
  intro i
  fin_cases i
  · exact checked03Lower_00
  · exact checked03Lower_01
  · exact checked03Lower_02
  · exact checked03Lower_03
  · exact checked03Lower_04
  · exact checked03Lower_05
  · exact checked03Lower_06
  · exact checked03Lower_07
  · exact checked03Lower_08


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity03Lower : slackRowsIdentityCheck 3 (-1) certificate03Lower rows03Lower=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted03Lower : certificate03Lower.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive03Lower {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 3 (-1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate03Lower rows03Lower rowsChecked03Lower identity03Lower accepted03Lower hz hz1 ha

end polyak.Certificates.P1Slacks
