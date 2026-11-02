import krylov.Envelope.AbsorbedStepShadow
import krylov.Envelope.PositiveReferenceOperator

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), genuine positive physical shadow recorded-step jets.
Use: derive every actual recorded-step first variation on real absorbed
physical scenarios from the true single-quadratic CG shadow, with
all actual matrix and active domains discharged.
Source: actual positive Gram operator curve, genuine absorbed physical
first jets and the true recorded-step moving-shadow transfer.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability krylov.Secant Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual recorded-step derivative on a true symmetric absorbed physical scenario equals the genuine CG step derivative on its constructed positive single-quadratic shadow.
Use: Every actual recorded-step derivative on a true symmetric absorbed physical scenario equals the genuine CG step derivative on its constructed positive single-quadratic shadow.
Article: main_krylov, apB:lem:mu(c), genuine positive physical shadow recorded-step jets.
Proof: Construct the actual positive Gram shadow with its true total physical increment first jet, derive every real matrix and active domain, and apply the genuine recorded-step information fibre. -/
theorem actual_absorbed_physical_step
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient (cgOperator base) g i≠0)
    (hsmooth : SmoothProbedCycleAt m 2 (cgOperator base) g N)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (hD : ∀ l < N-1, (D l).IsSymm)
    (hkill : ∀ l < N-1, ∀ i≤l, cgOperator (D l) (CG.gradient (cgOperator base) g i)=0)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB0 : B 0=fun _ => cgOperator base) (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0) (k : ℕ) (hk : k<N) :
    deriv (fun t => probedStep m (cumulativeOraclePath (cgOperator base) (fun l => cgOperator (D l)) t) (B t) g k) 0=
      deriv (fun t => referenceStep (positiveReferenceOperator base (∑ l∈Finset.range (N-1),D l) t) g k) 0 := by
  -- Construct a genuine positive quadratic shadow with the true total physical increment derivative and derive its actual active neighborhood.
  let T := positiveReferenceOperator base (∑ l∈Finset.range (N-1),D l)
  have h0 : T 0=cgOperator base := positiveReferenceOperator_zero _ _
  have hsym : (∑ l∈Finset.range (N-1),D l).IsSymm := by
    change (∑ l∈Finset.range (N-1),D l)ᵀ=∑ l∈Finset.range (N-1),D l
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl (fun l hl => (hD l (Finset.mem_range.mp hl)).eq)
  have hdT : HasDerivAt T (∑ l∈Finset.range (N-1),cgOperator (D l)) 0 := by
    simpa only [cgOperator,map_sum] using positiveReferenceOperator_hasDeriv base (∑ l∈Finset.range (N-1),D l)
  have hDop (l : ℕ) (hl : l < N-1) : (cgOperator (D l)).toLinearMap.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr (hD l hl))
  have he := actual_absorbed_shadow_step m hm T (fun l => cgOperator (D l)) g N
    (by rw [h0];exact (cgOperator_positive base hb).1) (by rw [h0];exact (cgOperator_positive base hb).2)
    (by rw [h0];exact hpre) (by rw [h0];exact hsmooth) (positiveReferenceOperator_analytic _ _ 0) hdT
    (positiveReferenceOperator_eventually_active base _ hb hsym g N hpre) hDop
    (by rw [h0];exact hkill) B (by rw [h0];exact hB0) hB k hk
  rw [h0] at he
  exact he
end
end krylov.Envelope
