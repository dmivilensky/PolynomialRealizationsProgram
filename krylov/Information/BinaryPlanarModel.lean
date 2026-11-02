import krylov.Tensor.BinaryGradientWitness
import krylov.Information.PlanarTerminalExecution

/-!
Article: main_krylov, thm:H, the genuine compatible binary planar model.
Use: construct the actual first/last tensor-slice operator path, with its
unknown rank-one base and true terminal correction operator. All intermediate
increments vanish in the observed first/last plane. Source: Appendix G,
equations (apD:eq:slice), (eq:planar-compression), (apD:eq:lastprobe).
-/

namespace krylov.Information
noncomputable section
open Real Matrix Finset krylov.Tensor krylov.Tensor.BinaryCubic krylov.Secant
  krylov.Reference krylov.LinearAlgebra krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A real scalar sequence with only the first and last midpoint increments.
Article: main_krylov, thm:H, tensor support in the first/last CG plane. -/
def binaryFirstLast (N : ℕ) (a b : ℝ) (j : ℕ) : ℝ :=
  (if j = 0 then a else 0) + (if j = N-1 then b else 0)

/-- The full actual first/last scalar path sums to its two endpoint increments.
Article: main_krylov, thm:H, actual accumulated tensor slices. -/
theorem binaryFirstLast_sum (N : ℕ) (hN : 0 < N) (a b : ℝ) :
    (∑ j ∈ range N, binaryFirstLast N a b j) = a+b := by
  simp [binaryFirstLast, sum_add_distrib, hN, Nat.sub_lt hN (by norm_num : 0 < 1)]

/-- The actual compatible planar secant path, whose hidden base cancels the final diagonal probe.
Article: main_krylov, thm:H, all observed model operators. -/
def binaryPlanarSegments (e h : EuclideanSpace ℝ (Fin n))
    (κ r : ℝ) (N : ℕ) (t : BinaryCubic) (j : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  terminalSegments e h
    (binaryFirstLast N (κ*t.t1) (κ*r*t.t2))
    (binaryFirstLast N (κ*t.t0) (κ*r*t.t1))
    (binaryFirstLast N (κ*t.t2) (κ*r*t.t3)) N j

/-- The true final gradient-query operator, including the final compatible tensor slice.
Article: main_krylov, thm:H, B=A0+T[zeta0]. -/
def binaryPlanarOutput (e h : EuclideanSpace ℝ (Fin n))
    (κ r : ℝ) (N : ℕ) (t : BinaryCubic) : Matrix (Fin n) (Fin n) ℝ :=
  binaryPlanarSegments e h κ r N t N + planarMatrix e h (κ*r*t.t1) (κ*r*t.t2) (κ*r*t.t3)

/-- The physical compatible planar source, transported by the true reference root.
Article: main_krylov, thm:H, the original physical operator model. -/
def binaryPlanarProbe (A : Matrix (Fin n) (Fin n) ℝ) (e h : EuclideanSpace ℝ (Fin n))
    (κ r : ℝ) (N : ℕ) (t : BinaryCubic) (j : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  cgOperator (metricRoot A * binaryPlanarSegments e h κ r N t j * metricRoot A)

/-- The actual base is exactly the unknown rank-one h-diagonal stipulated in the source.
Article: main_krylov, thm:H, beta=-k*(t2+r*t3). -/
theorem binaryPlanarSegments_base (e h : EuclideanSpace ℝ (Fin n))
    (κ r : ℝ) (N : ℕ) (hN : 0 < N) (t : BinaryCubic) :
    binaryPlanarSegments e h κ r N t 0 =
      1 + planarMatrix e h 0 0 (-κ*(t.t2+r*t.t3)) := by
  simp only [binaryPlanarSegments, terminalSegments, sum_range_zero, binaryFirstLast_sum N hN,
    zero_sub, planarMatrix, zero_smul, zero_add, add_zero]
  congr 2
  ring

/-- The exact compatible final planar operator has the source's three real entries.
Article: main_krylov, thm:H, compressed correction operator. -/
theorem binaryPlanarOutput_eq (e h : EuclideanSpace ℝ (Fin n))
    (κ r : ℝ) (N : ℕ) (hN : 0 < N) (t : BinaryCubic) :
    binaryPlanarOutput e h κ r N t =
      1 + planarMatrix e h (κ*(t.t0+2*r*t.t1)) (κ*(t.t1+2*r*t.t2)) (κ*r*t.t3) := by
  simp only [binaryPlanarOutput, binaryPlanarSegments, terminalSegments,
    binaryFirstLast_sum N hN, sub_self, planarMatrix, add_smul, mul_smul]
  module

/-- The signed binary witnesses have the source's literal common mean plus signed hidden completion.
Article: main_krylov, thm:H, actual M plus/minus Delta. -/
theorem binaryPlanarOutput_witness (e h : EuclideanSpace ℝ (Fin n))
    (κ r σ : ℝ) (N : ℕ) (hN : 0 < N) :
    let ψ := κ / (sqrt 2 * (1+r))
    binaryPlanarOutput e h κ r N (gradientWitness r σ) =
      (1 + planarMatrix e h (2*r*ψ) ψ (-r*ψ)) +
        σ • planarMatrix e h ((1+2*r^2)*ψ) (-r*ψ) 0 := by
  rw [binaryPlanarOutput_eq e h κ r N hN]
  simp only [gradientWitness, planarMatrix, smul_add, smul_smul]
  module

/-- Every observed last probe depends on the binary tensor through the actual cross combination t1+r*t2 alone.
Article: main_krylov, thm:H, the original gradient-only observation. -/
theorem binaryPlanarSegments_last_probe (e h : EuclideanSpace ℝ (Fin n))
    (hh : ‖h‖ = 1) (heh : inner ℝ e h = 0)
    (κ r : ℝ) (N : ℕ) (hN : 0 < N) (t : BinaryCubic) :
    cgOperator (binaryPlanarSegments e h κ r N t N) h = h + (κ*(t.t1+r*t.t2)) • e := by
  rw [binaryPlanarSegments, cgOperator, terminalSegments_last_probe e h hh heh, binaryFirstLast_sum N hN]
  congr 2
  ring

end
end krylov.Information
