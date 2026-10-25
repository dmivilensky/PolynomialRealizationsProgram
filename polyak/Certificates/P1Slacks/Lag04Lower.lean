import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 4, sign -1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate04Lower : Certificate where
  degree0 := 10
  degree1 := 5
  coefficient := ![
    ![16,80,160,160,80,16],
    ![160,800,1600,1600,800,160],
    ![(2835/4),(14157/4),(14139/2),(14121/2),(14103/4),(2817/4)],
    ![1830,9114,18156,18084,9006,1794],
    ![(194961/64),(1933563/128),(1917597/64),(118857/4),(471477/32),(374037/128)],
    ![(109107/32),(1075185/64),(1059543/32),(65259/2),(257247/16),(202815/64)],
    ![(165855/64),(25911849/2048),(101226081/4096),(98884713/4096),(48312375/4096),(9444765/4096)],
    ![(21045/16),(3245385/512),(12520929/1024),(12088425/1024),(5842743/1024),(1131357/1024)],
    ![(27135/64),(2053683/1024),(7787331/2048),(473910939/131072),(56566125/32768),(43443801/131072)],
    ![(2483/32),(182881/512),(676993/1024),(40442395/65536),(4774541/16384),(3659737/65536)],
    ![(385/64),(54409/2048),(194785/4096),(5704955/131072),(670933/32768),(8350265/2097152)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row04Lower_00 : Expr := (.add (.literal (16)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Lower_00 :
    (certificate04Lower.rowExpression ⟨0,by decide⟩).check row04Lower_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row04Lower_01 : Expr := (.add (.literal (160)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Lower_01 :
    (certificate04Lower.rowExpression ⟨1,by decide⟩).check row04Lower_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row04Lower_02 : Expr := (.add (.literal ((2835/4))) (.mul .y (.add (.literal ((-9/2))) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Lower_02 :
    (certificate04Lower.rowExpression ⟨2,by decide⟩).check row04Lower_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row04Lower_03 : Expr := (.add (.literal (1830)) (.mul .y (.add (.literal (-36)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Lower_03 :
    (certificate04Lower.rowExpression ⟨3,by decide⟩).check row04Lower_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row04Lower_04 : Expr := (.add (.literal ((194961/64))) (.mul .y (.add (.literal ((-16047/128))) (.mul .y (.add (.literal ((81/64))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Lower_04 :
    (certificate04Lower.rowExpression ⟨4,by decide⟩).check row04Lower_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row04Lower_05 : Expr := (.add (.literal ((109107/32))) (.mul .y (.add (.literal ((-15885/64))) (.mul .y (.add (.literal ((243/32))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Lower_05 :
    (certificate04Lower.rowExpression ⟨5,by decide⟩).check row04Lower_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row04Lower_06 : Expr := (.add (.literal ((165855/64))) (.mul .y (.add (.literal ((-624951/2048))) (.mul .y (.add (.literal ((78489/4096))) (.mul .y (.add (.literal ((729/2048))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Lower_06 :
    (certificate04Lower.rowExpression ⟨6,by decide⟩).check row04Lower_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row04Lower_07 : Expr := (.add (.literal ((21045/16))) (.mul .y (.add (.literal ((-121815/512))) (.mul .y (.add (.literal ((26649/1024))) (.mul .y (.add (.literal ((729/512))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Lower_07 :
    (certificate04Lower.rowExpression ⟨7,by decide⟩).check row04Lower_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row04Lower_08 : Expr := (.add (.literal ((27135/64))) (.mul .y (.add (.literal ((-117117/1024))) (.mul .y (.add (.literal ((41067/2048))) (.mul .y (.add (.literal ((247131/131072))) (.mul .y (.add (.literal ((-6561/65536))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Lower_08 :
    (certificate04Lower.rowExpression ⟨8,by decide⟩).check row04Lower_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row04Lower_09 : Expr := (.add (.literal ((2483/32))) (.mul .y (.add (.literal ((-15759/512))) (.mul .y (.add (.literal ((8505/1024))) (.mul .y (.add (.literal ((60507/65536))) (.mul .y (.add (.literal ((-6561/32768))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Lower_09 :
    (certificate04Lower.rowExpression ⟨9,by decide⟩).check row04Lower_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row04Lower_10 : Expr := (.add (.literal ((385/64))) (.mul .y (.add (.literal ((-7191/2048))) (.mul .y (.add (.literal ((5913/4096))) (.mul .y (.add (.literal ((13851/131072))) (.mul .y (.add (.literal ((-6561/65536))) (.mul .y (.add (.literal ((59049/2097152))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked04Lower_10 :
    (certificate04Lower.rowExpression ⟨10,by decide⟩).check row04Lower_10=true := by kernel_decide

def rows04Lower : Fin (certificate04Lower.degree0+1) → Expr := ![row04Lower_00,row04Lower_01,row04Lower_02,row04Lower_03,row04Lower_04,row04Lower_05,row04Lower_06,row04Lower_07,row04Lower_08,row04Lower_09,row04Lower_10]

theorem rowsChecked04Lower : ∀ i, (certificate04Lower.rowExpression i).check (rows04Lower i)=true := by
  intro i
  fin_cases i
  · exact checked04Lower_00
  · exact checked04Lower_01
  · exact checked04Lower_02
  · exact checked04Lower_03
  · exact checked04Lower_04
  · exact checked04Lower_05
  · exact checked04Lower_06
  · exact checked04Lower_07
  · exact checked04Lower_08
  · exact checked04Lower_09
  · exact checked04Lower_10


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity04Lower : slackRowsIdentityCheck 4 (-1) certificate04Lower rows04Lower=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted04Lower : certificate04Lower.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive04Lower {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 4 (-1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate04Lower rows04Lower rowsChecked04Lower identity04Lower accepted04Lower hz hz1 ha

end polyak.Certificates.P1Slacks
