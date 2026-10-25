import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 6, sign 1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate06Upper : Certificate where
  degree0 := 10
  degree1 := 5
  coefficient := ![
    ![16,80,160,160,80,16],
    ![160,800,1600,1600,800,160],
    ![(2835/4),(14193/4),(14193/2),(14175/2),(14139/4),(2817/4)],
    ![1830,9186,18372,18300,9078,1794],
    ![(390003/128),(1965657/128),(1965495/64),(1949529/64),(1917759/128),(374037/128)],
    ![(218457/64),(1106955/64),(1106469/32),(1090827/32),(1060029/64),(202815/64)],
    ![(332925/128),(54327147/4096),(54249387/2048),(13259409/512),(25347405/2048),(9444765/4096)],
    ![(42495/32),(6981675/1024),(6955755/512),(1681089/128),(3145197/512),(1131357/1024)],
    ![(55485/128),(4586769/2048),(4547889/1024),(554323419/131072),(31550031/16384),(43443801/131072)],
    ![(5209/64),(432443/1024),(424667/512),(50694619/65536),(2795695/8192),(3659737/65536)],
    ![(851/128),(141227/4096),(136043/2048),(7872731/131072),(419783/16384),(8350265/2097152)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row06Upper_00 : Expr := (.add (.literal (16)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Upper_00 :
    (certificate06Upper.rowExpression ⟨0,by decide⟩).check row06Upper_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row06Upper_01 : Expr := (.add (.literal (160)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Upper_01 :
    (certificate06Upper.rowExpression ⟨1,by decide⟩).check row06Upper_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row06Upper_02 : Expr := (.add (.literal ((2835/4))) (.mul .y (.add (.literal ((9/2))) (.mul .y (.add (.literal (-9)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Upper_02 :
    (certificate06Upper.rowExpression ⟨2,by decide⟩).check row06Upper_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row06Upper_03 : Expr := (.add (.literal (1830)) (.mul .y (.add (.literal (36)) (.mul .y (.add (.literal (-72)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Upper_03 :
    (certificate06Upper.rowExpression ⟨3,by decide⟩).check row06Upper_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row06Upper_04 : Expr := (.add (.literal ((390003/128))) (.mul .y (.add (.literal ((7821/64))) (.mul .y (.add (.literal ((-3951/16))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Upper_04 :
    (certificate06Upper.rowExpression ⟨4,by decide⟩).check row06Upper_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row06Upper_05 : Expr := (.add (.literal ((218457/64))) (.mul .y (.add (.literal ((7335/32))) (.mul .y (.add (.literal ((-3789/8))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Upper_05 :
    (certificate06Upper.rowExpression ⟨5,by decide⟩).check row06Upper_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row06Upper_06 : Expr := (.add (.literal ((332925/128))) (.mul .y (.add (.literal ((1059147/4096))) (.mul .y (.add (.literal ((-1136907/2048))) (.mul .y (.add (.literal ((729/512))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Upper_06 :
    (certificate06Upper.rowExpression ⟨6,by decide⟩).check row06Upper_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row06Upper_07 : Expr := (.add (.literal ((42495/32))) (.mul .y (.add (.literal ((182475/1024))) (.mul .y (.add (.literal ((-208395/512))) (.mul .y (.add (.literal ((729/128))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Upper_07 :
    (certificate06Upper.rowExpression ⟨7,by decide⟩).check row06Upper_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row06Upper_08 : Expr := (.add (.literal ((55485/128))) (.mul .y (.add (.literal ((147969/2048))) (.mul .y (.add (.literal ((-186849/1024))) (.mul .y (.add (.literal ((1086939/131072))) (.mul .y (.add (.literal ((6561/65536))) (.mul .y (.add (.literal ((-6561/32768))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Upper_08 :
    (certificate06Upper.rowExpression ⟨8,by decide⟩).check row06Upper_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row06Upper_09 : Expr := (.add (.literal ((5209/64))) (.mul .y (.add (.literal ((15723/1024))) (.mul .y (.add (.literal ((-23499/512))) (.mul .y (.add (.literal ((340443/65536))) (.mul .y (.add (.literal ((6561/32768))) (.mul .y (.add (.literal ((-6561/16384))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Upper_09 :
    (certificate06Upper.rowExpression ⟨9,by decide⟩).check row06Upper_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row06Upper_10 : Expr := (.add (.literal ((851/128))) (.mul .y (.add (.literal ((5067/4096))) (.mul .y (.add (.literal ((-10251/2048))) (.mul .y (.add (.literal ((153819/131072))) (.mul .y (.add (.literal ((6561/65536))) (.mul .y (.add (.literal ((-360855/2097152))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Upper_10 :
    (certificate06Upper.rowExpression ⟨10,by decide⟩).check row06Upper_10=true := by kernel_decide

def rows06Upper : Fin (certificate06Upper.degree0+1) → Expr := ![row06Upper_00,row06Upper_01,row06Upper_02,row06Upper_03,row06Upper_04,row06Upper_05,row06Upper_06,row06Upper_07,row06Upper_08,row06Upper_09,row06Upper_10]

theorem rowsChecked06Upper : ∀ i, (certificate06Upper.rowExpression i).check (rows06Upper i)=true := by
  intro i
  fin_cases i
  · exact checked06Upper_00
  · exact checked06Upper_01
  · exact checked06Upper_02
  · exact checked06Upper_03
  · exact checked06Upper_04
  · exact checked06Upper_05
  · exact checked06Upper_06
  · exact checked06Upper_07
  · exact checked06Upper_08
  · exact checked06Upper_09
  · exact checked06Upper_10


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity06Upper : slackRowsIdentityCheck 6 (1) certificate06Upper rows06Upper=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted06Upper : certificate06Upper.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive06Upper {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 6 (1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate06Upper rows06Upper rowsChecked06Upper identity06Upper accepted06Upper hz hz1 ha

end polyak.Certificates.P1Slacks
