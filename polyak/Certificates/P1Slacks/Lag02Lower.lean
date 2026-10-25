import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 2, sign -1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate02Lower : Certificate where
  degree0 := 6
  degree1 := 3
  coefficient := ![
    ![4,12,12,4],
    ![24,72,72,24],
    ![(471/8),(1413/8),(1413/8),(471/8)],
    ![(151/2),(453/2),(453/2),(151/2)],
    ![(213/4),(40815/256),(20367/128),(13551/256)],
    ![(39/2),(7407/128),(3663/64),(2415/128)],
    ![(23/8),(2127/256),(1023/128),(21689/8192)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row02Lower_00 : Expr := (.add (.literal (4)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked02Lower_00 :
    (certificate02Lower.rowExpression ⟨0,by decide⟩).check row02Lower_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row02Lower_01 : Expr := (.add (.literal (24)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked02Lower_01 :
    (certificate02Lower.rowExpression ⟨1,by decide⟩).check row02Lower_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row02Lower_02 : Expr := (.add (.literal ((471/8))) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked02Lower_02 :
    (certificate02Lower.rowExpression ⟨2,by decide⟩).check row02Lower_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row02Lower_03 : Expr := (.add (.literal ((151/2))) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked02Lower_03 :
    (certificate02Lower.rowExpression ⟨3,by decide⟩).check row02Lower_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row02Lower_04 : Expr := (.add (.literal ((213/4))) (.mul .y (.add (.literal ((-81/256))) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked02Lower_04 :
    (certificate02Lower.rowExpression ⟨4,by decide⟩).check row02Lower_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row02Lower_05 : Expr := (.add (.literal ((39/2))) (.mul .y (.add (.literal ((-81/128))) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked02Lower_05 :
    (certificate02Lower.rowExpression ⟨5,by decide⟩).check row02Lower_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row02Lower_06 : Expr := (.add (.literal ((23/8))) (.mul .y (.add (.literal ((-81/256))) (.mul .y (.add (.literal (0)) (.mul .y (.add (.literal ((729/8192))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked02Lower_06 :
    (certificate02Lower.rowExpression ⟨6,by decide⟩).check row02Lower_06=true := by kernel_decide

def rows02Lower : Fin (certificate02Lower.degree0+1) → Expr := ![row02Lower_00,row02Lower_01,row02Lower_02,row02Lower_03,row02Lower_04,row02Lower_05,row02Lower_06]

theorem rowsChecked02Lower : ∀ i, (certificate02Lower.rowExpression i).check (rows02Lower i)=true := by
  intro i
  fin_cases i
  · exact checked02Lower_00
  · exact checked02Lower_01
  · exact checked02Lower_02
  · exact checked02Lower_03
  · exact checked02Lower_04
  · exact checked02Lower_05
  · exact checked02Lower_06


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity02Lower : slackRowsIdentityCheck 2 (-1) certificate02Lower rows02Lower=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted02Lower : certificate02Lower.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive02Lower {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 2 (-1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate02Lower rows02Lower rowsChecked02Lower identity02Lower accepted02Lower hz hz1 ha

end polyak.Certificates.P1Slacks
