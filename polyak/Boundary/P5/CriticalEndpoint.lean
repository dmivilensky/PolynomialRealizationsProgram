import polyak.Boundary.P5.CriticalSolution
import polyak.Certificates.P5Critical
import polyak.Certificates.Continuation.P5Batches.Batch000
import polyak.Numerics.KernelDecide

/-! The exact algebraic critical solution lies in the first global continuation box. -/
noncomputable section
namespace polyak.Boundary.P5
open LeanCert.Core LeanCert.Engine Numerics Numerics.Parametric Polynomial

private def initialBox := coordinateBox Certificates.Continuation.P5.Batch000.C0.center
  Certificates.Continuation.P5.Batch000.C0.radius

private theorem critical_mem_polynomial {P : ℚ[X]} (code : PolynomialCode P) (i : Fin 7)
    (hl : QPoly.bernsteinCheck .strictLower code.code (initialBox i).lo criticalInterval 0=true)
    (hu : QPoly.bernsteinCheck .strictUpper code.code (initialBox i).hi criticalInterval 0=true) :
    aeval y₀ P∈initialBox i := by
  have hlo := QPoly.lt_aeval_of_bernsteinCheck hl y₀ criticalRoot.mem
  have hhi := QPoly.aeval_lt_of_bernsteinCheck hu y₀ criticalRoot.mem
  rw [code.exact] at hlo hhi
  exact ⟨hlo.le,hhi.le⟩

theorem criticalPoint_mem : FinBoxMem criticalPoint initialBox := by
  intro i
  fin_cases i
  · exact critical_mem_polynomial Certificates.P5.ACode 0 (by kernel_decide) (by kernel_decide)
  · exact critical_mem_polynomial Certificates.P5.BCode 1 (by kernel_decide) (by kernel_decide)
  · change y₀∈initialBox 2
    have h := criticalRoot.mem
    change y₀∈criticalInterval at h
    norm_num [IntervalRat.mem_def,initialBox,coordinateBox,
      Certificates.Continuation.P5.Batch000.C0,IntervalRat.add,IntervalRat.singleton,
      symmetricInterval,criticalInterval] at h ⊢
    constructor <;> linarith
  · exact critical_mem_polynomial Certificates.P5.PCode 3 (by kernel_decide) (by kernel_decide)
  · exact critical_mem_polynomial Certificates.P5.DCode 4 (by kernel_decide) (by kernel_decide)
  · exact critical_mem_polynomial Certificates.P5.w2Code 5 (by kernel_decide) (by kernel_decide)
  · exact critical_mem_polynomial Certificates.P5.w3Code 6 (by kernel_decide) (by kernel_decide)

end polyak.Boundary.P5
