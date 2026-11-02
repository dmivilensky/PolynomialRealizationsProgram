import krylov.Envelope.AbsorbedShadow
import krylov.Envelope.PositiveReferenceOperator

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), genuine absorbed physical-scenario CG derivative.
Use: identify every actual smooth globally CG-consistent raw-method
gradient derivative on real absorbed symmetric physical increments with
the true derivative of one explicitly constructed positive quadratic CG run.
Source: actual analytic positive Gram shadow reference, true moving
quadratic fibre and genuine primitive finite-oracle first-jet transfer.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability krylov.Secant Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual primitive smooth globally CG-consistent raw-method gradient on real absorbed symmetric physical increments has exactly the true CG derivative on the explicitly constructed genuine positive quadratic shadow, including arbitrary actual differentiable correction paths.
Use: Every actual primitive smooth globally CG-consistent raw-method gradient on real absorbed symmetric physical increments has exactly the true CG derivative on the explicitly constructed genuine positive quadratic shadow, including arbitrary actual differentiable correction paths.
Article: main_krylov, apB:lem:mu(c), genuine absorbed physical-scenario CG derivative.
Proof: Construct the actual analytic positive Gram shadow with the genuine total increment derivative. Its real active neighborhood, actual CG regularity, true absorbed compression first jets and genuine oracle execution identity discharge all moving-shadow premises. -/
theorem actual_absorbed_physical_gradient
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient (cgOperator base) g i≠0)
    (hsmooth : SmoothProbedCycleAt m 2 (cgOperator base) g N)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (hD : ∀ l < N-1, (D l).IsSymm)
    (hkill : ∀ l < N-1, ∀ i≤l, cgOperator (D l) (CG.gradient (cgOperator base) g i)=0)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB0 : B 0=fun _ => cgOperator base) (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0) :
    deriv (fun t => probedGradient m (cumulativeOraclePath (cgOperator base) (fun l => cgOperator (D l)) t) (B t) g N) 0=
      deriv (fun t => CG.gradient (positiveReferenceOperator base (∑ l∈Finset.range (N-1),D l) t) g N) 0 := by
  -- Construct the actual positive quadratic shadow from the true physical increment sum and derive every genuine operator and active-prefix domain.
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
  have he := actual_absorbed_shadow_gradient m hm T (fun l => cgOperator (D l)) g N
    (by rw [h0];exact (cgOperator_positive base hb).1) (by rw [h0];exact (cgOperator_positive base hb).2)
    (by rw [h0];exact hpre) (by rw [h0];exact hsmooth) (positiveReferenceOperator_analytic _ _ 0) hdT
    (positiveReferenceOperator_eventually_active base _ hb hsym g N hpre) hDop
    (by rw [h0];exact hkill) B (by rw [h0];exact hB0) hB
  rw [h0] at he
  exact he
end
end krylov.Envelope
