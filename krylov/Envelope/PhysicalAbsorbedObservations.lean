import krylov.Envelope.AbsorbedObservationShadow
import krylov.Envelope.PositiveReferenceOperator

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), actual full-observation positive physical shadow.
Use: identify every actual observation first variation on genuine
absorbed physical increments with a constructed true positive quadratic
shadow, discharging all real shadow and reference domains.
Source: genuine analytic positive Gram curve and actual full-history
absorbed information fibre, with its true finite oracle first-jet transfer.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability krylov.Secant Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every genuine full-history observation coordinate on actual symmetric absorbed physical increments has exactly the true derivative of the constructed positive single-quadratic shadow transcript.
Use: Every genuine full-history observation coordinate on actual symmetric absorbed physical increments has exactly the true derivative of the constructed positive single-quadratic shadow transcript.
Article: main_krylov, apB:lem:mu(c), actual full-observation positive physical shadow.
Proof: Construct the actual positive Gram curve with the real total increment derivative. Its true active neighborhood and actual matrix symmetry discharge every genuine full-observation shadow domain. -/
theorem actual_absorbed_physical_observation
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient (cgOperator base) g i≠0)
    (hsmooth : SmoothProbedCycleAt m 2 (cgOperator base) g N)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (hD : ∀ l < N-1, (D l).IsSymm)
    (hkill : ∀ l < N-1, ∀ i≤l, cgOperator (D l) (CG.gradient (cgOperator base) g i)=0)
    (B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hB0 : B 0=fun _ => cgOperator base) (hB : ∀ i<N, DifferentiableAt ℝ (fun t => B t i) 0) (j : ℕ) :
    deriv (fun t => (methodRun m (cumulativeOraclePath (cgOperator base) (fun l => cgOperator (D l)) t) (B t) g N).observationList.getD j 0) 0=
      deriv (fun t => (methodRun m (fun _ => positiveReferenceOperator base (∑ l∈Finset.range (N-1),D l) t)
        (fun _ => positiveReferenceOperator base (∑ l∈Finset.range (N-1),D l) t) g N).observationList.getD j 0) 0 := by
  -- The actual positive Gram shadow has the genuine total physical increment first jet; its true active neighborhood is derived from the real reference.
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
  have he := actual_absorbed_shadow_observation m hm T (fun l => cgOperator (D l)) g N
    (by rw [h0];exact (cgOperator_positive base hb).1) (by rw [h0];exact (cgOperator_positive base hb).2)
    (by rw [h0];exact hpre) (by rw [h0];exact hsmooth) (positiveReferenceOperator_analytic _ _ 0) hdT
    (positiveReferenceOperator_eventually_active base _ hb hsym g N hpre) hDop
    (by rw [h0];exact hkill) B (by rw [h0];exact hB0) hB j
  rw [h0] at he
  exact he
end
end krylov.Envelope
