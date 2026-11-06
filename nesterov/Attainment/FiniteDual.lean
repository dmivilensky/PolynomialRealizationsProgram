import nesterov.Attainment.DualAtomic

/-! The actual limiting dual becomes a finite normalized lag combination
once one optimizer supplies a strict minimizer reserve and an active-lag bound. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal OnePoint
namespace nesterov.Attainment
open Spectral

structure FiniteDualExpansion {M : StationaryMethod} {μ L : ℝ} (B : BoundaryDual M μ L) (N : ℕ) where
  Index : Type
  [fintypeIndex : Fintype Index]
  weight : Index → ℝ≥0
  weight_sum : ∑ j,weight j=1
  lag : Index → ℕ
  lag_pos : ∀ j,1 ≤ lag j
  lag_le : ∀ j,lag j ≤ N
  sign : Index → ℝ
  sign_cases : ∀ j,sign j=1 ∨ sign j= -1
  symbol_eq : ∀ c : Frequency, B.symbol c =
    ∑ j,(weight j : ℝ) * ((lagA (M.symbolPair μ L (Closure.T M μ L)) B.frame.center (lag j) c-
      sign j*lagB (M.symbolPair μ L (Closure.T M μ L)) (lag j) c) /
        Real.sinh (lag j*(B.frame.center : ℝ)))

attribute [instance] FiniteDualExpansion.fintypeIndex

set_option backward.isDefEq.respectTransparency false in
theorem BoundaryDual.exists_finite_expansion {M : StationaryMethod} {μ L : ℝ}
    (B : BoundaryDual M μ L) {ν : Spectrum} {C : ℝ}
    (h : Feasible (M.symbolPair μ L (Closure.T M μ L)) (Closure.T M μ L) ν C)
    (hstar : |C| < meanG ν (M.symbolPair μ L (Closure.T M μ L)))
    {N : ℕ} (hN : ∀ n∈activeLags M μ L (Closure.T M μ L) ν C,n ≤ N) :
    Nonempty (FiniteDualExpansion B N) := by
  classical
  let F := finiteLagLabels N
  let : Fintype F := (finiteLagLabels_finite N).fintype
  obtain ⟨w,hw,he⟩ := exists_finiteDualMeasure_of_support B.Λ (B.measure_finite_lags h hstar hN)
  have hpre (j : F) : ∃ i : Bool × Fin N,(i.1,((i.2.val : ℕ) : OnePoint ℕ))=j.val := j.property
  let idx : F → Bool × Fin N := fun j => Classical.choose (hpre j)
  have hidx (j : F) : ((idx j).1,(((idx j).2.val : ℕ) : OnePoint ℕ))=j.val := Classical.choose_spec (hpre j)
  refine ⟨{
    Index := F
    weight := w
    weight_sum := hw
    lag := fun j => (idx j).2.val+1
    lag_pos := fun _ => Nat.succ_pos _
    lag_le := fun j => (idx j).2.isLt
    sign := fun j => if (idx j).1 then -1 else 1
    sign_cases := fun j => by cases (idx j).1 <;> simp
    symbol_eq := ?_ }⟩
  intro c
  let Lc := traceCLM B.frame.lo B.frame.hi B.frame.center
    (physicalAngle B.frame.lo (half_pos B.frame.radius_pos) c)
  have hrep := B.barycenter Lc
  rw [← he,finiteDualMeasure_integral] at hrep
  change (∑ j : F,(w j : ℝ)*Lc (B.generator j.val))=B.symbol c at hrep
  rw [← hrep]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [← hidx j]
  change ((dualFamily B.frame.lo B.frame.hi (half_pos B.frame.radius_pos)
    (gapEntireMap M.queryPolynomial (M.normalizedPolynomial μ L) B.frame.lo B.frame.hi B.frame.sign)
    (skewEntireMap M.queryPolynomial (M.normalizedPolynomial μ L) B.frame.lo B.frame.hi B.frame.sign)
    (if (idx j).1 then -1 else 1) ((idx j).2.val : OnePoint ℕ)).2
      (B.frame.center,physicalAngle B.frame.lo (half_pos B.frame.radius_pos) c)).re = _
  rw [dualFamily_physical_coe,Complex.ofReal_re,B.pair_eq]

end nesterov.Attainment
