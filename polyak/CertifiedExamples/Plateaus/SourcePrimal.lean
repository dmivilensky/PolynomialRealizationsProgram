import polyak.CertifiedExamples.Plateaus.SourceMatrix
import polyak.Certificates.PartII.Plateaus.PrimalNumerical

/-! The concrete rank and all essential strict primal constraints. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels Matrix LeanCert.Core chebyshev2.Numerics
open polyak.Certificates.PartII.Plateaus
open scoped BigOperators

theorem rank18 : sourceMatrix18.rank=1 := by
  apply rank_eq_of_kernel_minor sourceMatrix18 rho18
    (positivePrimal_kernel sourceMatrix18 0 sourceMatrix18_det_zero)
  · intro h
    have he:=congrFun h 0
    exact (rho18_positive 0).ne' he
  · have h:=enclosed_sound _ _ _ row18_rank_minor_checked (matrixPoint sourceMatrix18) matrixPoint18_mem
    have he : (row18MatrixVariables 1 1).value (matrixPoint sourceMatrix18)=
        (sourceMatrix18.submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_fin_one]
      exact matrixVariables_value sourceMatrix18 1 1
    rw [he] at h
    have hn:(row18RankMinor.hi:ℝ)<0:=by norm_num [row18RankMinor]
    exact (h.2.trans_lt hn).ne

theorem rank21 : sourceMatrix21.rank=2 := by
  apply rank_eq_of_kernel_minor sourceMatrix21 rho21
    (positivePrimal_kernel sourceMatrix21 0 sourceMatrix21_det_zero)
  · intro h
    have he:=congrFun h 0
    exact (rho21_positive 0).ne' he
  · have h:=enclosed_sound _ _ _ row21_rank_minor_checked (matrixPoint sourceMatrix21) matrixPoint21_mem
    have he : (det2Expr (fun i j=>row21MatrixVariables (Fin.succ i) (Fin.succ j))).value
        (matrixPoint sourceMatrix21)=(sourceMatrix21.submatrix Fin.succ Fin.succ).det := by
      rw [det2Expr_value]
      congr 1
      ext i j
      exact matrixVariables_value sourceMatrix21 i.succ j.succ
    rw [he] at h
    have hn:(row21RankMinor.hi:ℝ)<0:=by norm_num [row21RankMinor]
    exact (h.2.trans_lt hn).ne

def primalPoint18 : Fin 7→ℝ:=![coefficientVector tuning18 0,coefficientVector tuning18 1,
  coefficientVector tuning18 2,coordinates18 0,coordinates18 1,rho18 0,rho18 1]
def primalPoint21 : Fin 9→ℝ:=![coefficientVector tuning21 0,coefficientVector tuning21 1,
  coefficientVector tuning21 2,coordinates21 0,coordinates21 1,coordinates21 2,rho21 0,rho21 1,rho21 2]

theorem primalPoint18_mem : ∀i,primalPoint18 i∈row18PrimalBox i := by
  intro i
  fin_cases i
  · exact tuning18_Xi_mem 0
  · exact tuning18_Xi_mem 1
  · exact tuning18_Xi_mem 2
  · exact coordinates18_mem 0
  · exact coordinates18_mem 1
  · exact rho18_mem 0
  · exact rho18_mem 1

theorem primalPoint21_mem : ∀i,primalPoint21 i∈row21PrimalBox i := by
  intro i
  fin_cases i
  · exact tuning21_Xi_mem 0
  · exact tuning21_Xi_mem 1
  · exact tuning21_Xi_mem 2
  · exact coordinates21_mem 0
  · exact coordinates21_mem 1
  · exact coordinates21_mem 2
  · exact rho21_mem 0
  · exact rho21_mem 1
  · exact rho21_mem 2

theorem primalLag18_actual (n:ℤ) : (row18PrimalLagExpr n).value primalPoint18=
    ∑i,rho18 i*Farey.Certificates.signedLagPolynomial tuning18 n (coordinates18 i) := by
  rw [row18PrimalLagExpr,primalLag2Expr_value]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;>
    change rho18 _*coordinateLag (coefficientVector tuning18) n (coordinates18 _)=_ <;>
      rw [coordinateLag_actual_coefficients] <;> rfl

theorem primalLag21_actual (n:ℤ) : (row21PrimalLagExpr n).value primalPoint21=
    ∑i,rho21 i*Farey.Certificates.signedLagPolynomial tuning21 n (coordinates21 i) := by
  rw [row21PrimalLagExpr,primalLag3Expr_value]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;>
    change rho21 _*coordinateLag (coefficientVector tuning21) n (coordinates21 _)=_ <;>
      rw [coordinateLag_actual_coefficients] <;> rfl

theorem primalMin18_actual : row18PrimalMinExpr.value primalPoint18=
    ∑i,rho18 i*tuning18.Xi (coordinates18 i) := by
  rw [row18PrimalMinExpr,primalMin2Expr_value]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;>
    change rho18 _*coefficientValue (coefficientVector tuning18) (coordinates18 _)=_ <;>
      rw [coefficientVector_actual] <;> rfl

theorem primalMin21_actual : row21PrimalMinExpr.value primalPoint21=
    ∑i,rho21 i*tuning21.Xi (coordinates21 i) := by
  rw [row21PrimalMinExpr,primalMin3Expr_value]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;>
    change rho21 _*coefficientValue (coefficientVector tuning21) (coordinates21 _)=_ <;>
      rw [coefficientVector_actual] <;> rfl

private theorem positive_value_of_check {d:ℕ} (e:E d) (box:Fin d→IntervalRat)
    (hc:(IntervalExpr.neg e).strictNegative box=true) (v:Fin d→ℝ) (hv:∀i,v i∈box i) :
    0<e.value v := by
  have h:=(IntervalExpr.neg e).strictNegative_sound box hc hv
  change -e.value v<0 at h
  linarith

theorem inactive18 (r:ℤ) (hr:0<r) (hL:r<18)
    (hne:∀i:Fin 2,r≠(![1,14]:Fin 2→ℤ) i) :
    0<∑i,rho18 i*Farey.Certificates.signedLagPolynomial tuning18 r (coordinates18 i) := by
  have h1:r≠1:=by simpa using hne 0
  have h14:r≠14:=by simpa using hne 1
  let n:Fin 18:=⟨r.toNat,by omega⟩
  have hcast:(n.val:ℤ)=r:=Int.toNat_of_nonneg hr.le
  have hc:=row18_inactive_checked n (by omega) (by omega) (by omega)
  have hp:=positive_value_of_check _ _ hc primalPoint18 primalPoint18_mem
  rw [primalLag18_actual,hcast] at hp
  exact hp

theorem inactive21 (r:ℤ) (hr:0<r) (hL:r<21)
    (hne:∀i:Fin 3,r≠(![1,9,17]:Fin 3→ℤ) i) :
    0<∑i,rho21 i*Farey.Certificates.signedLagPolynomial tuning21 r (coordinates21 i) := by
  have h1:r≠1:=by simpa using hne 0
  have h9:r≠9:=by simpa using hne 1
  have h17:r≠17:=by simpa using hne 2
  let n:Fin 21:=⟨r.toNat,by omega⟩
  have hcast:(n.val:ℤ)=r:=Int.toNat_of_nonneg hr.le
  have hc:=row21_inactive_checked n (by omega) (by omega) (by omega) (by omega)
  have hp:=positive_value_of_check _ _ hc primalPoint21 primalPoint21_mem
  rw [primalLag21_actual,hcast] at hp
  exact hp

theorem minimizer18 : 0<∑i,rho18 i*tuning18.Xi (coordinates18 i) := by
  rw [←primalMin18_actual]
  exact positive_value_of_check _ _ row18_minimizer_positive_checked primalPoint18 primalPoint18_mem

theorem minimizer21 : 0<∑i,rho21 i*tuning21.Xi (coordinates21 i) := by
  rw [←primalMin21_actual]
  exact positive_value_of_check _ _ row21_minimizer_positive_checked primalPoint21 primalPoint21_mem

end polyak.CertifiedExamples.Plateaus
