import krylov.Envelope.CanonicalFiltration
import krylov.Variation.FCResponse

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), genuine canonical absorbed increments.
Use: express source absorption on the actual explored canonical CG flags
and derive true physical symmetry and old-gradient annihilation for the
real changing-operator quadratic information shadow.
Source: genuine positive-root Krylov flag identification, actual CG
gradient spans and true finite physical increment congruence.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Variation Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true source absorbed-increment property on the actual explored canonical CG flags.
Use: The true source absorbed-increment property on the actual explored canonical CG flags.
Article: main_krylov, apB:lem:mu(c), genuine canonical absorbed increments.
Proof: Every genuine increment kills its true earlier explored flag. -/
def AbsorbedIncrements (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) : Prop :=
  ∀ l<N-1, ∀ v∈exploredFlag base g (l+1), cgOperator (E l) v=0

/-- The genuine physical matrix increments of the actual canonical source scenario.
Use: The genuine physical matrix increments of the actual canonical source scenario.
Article: main_krylov, apB:lem:mu(c), genuine canonical absorbed increments.
Proof: Apply the true reference positive-root congruence to each real canonical increment. -/
def physicalIncrements (base : Matrix (Fin n) (Fin n) ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (l : ℕ) :
    Matrix (Fin n) (Fin n) ℝ := metricRoot base*E l*metricRoot base

/-- Actual symmetric canonical increments give genuine symmetric physical increments.
Use: Actual symmetric canonical increments give genuine symmetric physical increments.
Article: main_krylov, apB:lem:mu(c), genuine canonical absorbed increments.
Proof: Transpose the true positive-root congruence and use actual symmetry of its real factors. -/
theorem physicalIncrements_symm (base : Matrix (Fin n) (Fin n) ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (l : ℕ) (hE : (E l).IsSymm) : (physicalIncrements base E l).IsSymm := by
  change (metricRoot base*E l*metricRoot base)ᵀ=metricRoot base*E l*metricRoot base
  simp only [Matrix.transpose_mul,(metricRoot_isSymm base).eq,hE.eq,Matrix.mul_assoc]

/-- Every genuine absorbed canonical increment annihilates exactly the true required old physical CG gradients after actual positive-root congruence.
Use: Every genuine absorbed canonical increment annihilates exactly the true required old physical CG gradients after actual positive-root congruence.
Article: main_krylov, apB:lem:mu(c), genuine canonical absorbed increments.
Proof: The real active reference gradients span their genuine polynomial Krylov flag. Its actual positive-root image is exactly the true canonical explored flag, so genuine absorption kills the real middle increment action. -/
theorem physicalIncrements_kill_gradients (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient (cgOperator base) g i≠0) (habs : AbsorbedIncrements base g E N)
    (l : ℕ) (hl : l<N-1) (i : ℕ) (hi : i≤l) :
    cgOperator (physicalIncrements base E l) (CG.gradient (cgOperator base) g i)=0 := by
  -- Place actual old CG gradients in their true polynomial Krylov flag before using the genuine canonical absorption hypothesis.
  let Q := cgOperator base
  have hline (j : ℕ) (hj : j<l+1) : CG.length Q g j≠0 :=
    (CG.invariant_line_pos Q (cgOperator_positive base hb).2 g j
      (CG.invariant Q (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g j
        (fun r hr => hpre r (by omega))) (hpre j (by omega))).2.1.ne'
  have hK : CG.gradient Q g i∈CG.krylovSpace Q g (l+1) := by
    rw [CG.krylovSpace_eq_span_gradients Q g (l+1) hline]
    exact Submodule.subset_span ⟨i,(by change i < l+1;omega),rfl⟩
  have hR : cgOperator (metricRoot base) (CG.gradient Q g i)∈exploredFlag base g (l+1) := by
    rw [exploredFlag_eq_primal_krylov base hb g (l+1) (fun j hj => hpre j (by omega))]
    exact Submodule.mem_map_of_mem hK
  have hz := habs l hl _ hR
  change cgOperator (metricRoot base*E l*metricRoot base) (CG.gradient Q g i)=0
  simp only [cgOperator,map_mul,mul_apply_eq_comp]
  change cgOperator (metricRoot base) (cgOperator (E l) (cgOperator (metricRoot base) (CG.gradient Q g i)))=0
  rw [hz,map_zero]

/-- The true finite sum of actual physical increment operators equals the genuine canonical cumulative segment drift.
Use: The true finite sum of actual physical increment operators equals the genuine canonical cumulative segment drift.
Article: main_krylov, apB:lem:mu(c), genuine canonical absorbed increments.
Proof: Distribute the actual positive-root congruence and true matrix/operator linear identification through the genuine finite sum. -/
theorem cumulative_physicalIncrements (base : Matrix (Fin n) (Fin n) ℝ)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    (∑ l∈Finset.range k,cgOperator (physicalIncrements base E l))=cumulativeDrift base E k := by
  simp only [physicalIncrements,cumulativeDrift,cgOperator,Matrix.mul_sum,Matrix.sum_mul,map_sum]
end
end krylov.Envelope
