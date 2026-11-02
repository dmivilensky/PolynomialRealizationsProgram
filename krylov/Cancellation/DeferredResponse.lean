import krylov.Envelope.FreshDefectCoordinates
import krylov.Envelope.FlagOrthogonality
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, original full deferred spatial response.
Use: define the printed true last-step/weighted-prior-tail vectors and
identify their genuine physical residual coordinates and explored flag.
Source: actual canonical CG steps, reused finite-prefix FC response and
fresh-defect coordinate identities, and true finite linear projection calculus.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Variation krylov.Envelope
open scoped BigOperators
variable {n : ℕ}

/-- The source's genuine last-step plus damped old-tail vector for increment l.
Use: the reference damping value is independent of the estimate's derivative.
Article: main_krylov, thm:DC, vtilde_l. -/
def deferredTail (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (epsilon : ℝ) (l : ℕ) : EuclideanSpace ℝ (Fin n) :=
  epsilon • (∑ j∈Ico (l+1) k,canonicalCGStep base g j)+canonicalCGStep base g k

/-- The original deferred first-order spatial response on actual CG flags.
Use: connect actual executed residual coordinates to sharp original matrix budgets.
Article: main_krylov, thm:DC, sum P_l E_l vtilde_l. -/
def deferredResponse (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (epsilon : ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) : EuclideanSpace ℝ (Fin n) :=
  ∑ l∈range k,(oldFlag base g l).starProjection (cgOperator (E l) (deferredTail base g k epsilon l))

/-- The literal original deferred spatial response is the genuine damped
pre-final FC response plus the actual square-root-energy fresh response.
Use: reuse both earlier real coordinate reconstructions without introducing
an independent desired residual or an arbitrary canonical frame.
Article: main_krylov, thm:DC.
Proof: the actual final canonical step is its true norm times its genuine
unit direction; real linear projection distributes each finite tail sum. -/
theorem deferred_response_split (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (epsilon : ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    deferredResponse base g k epsilon E=
      epsilon • partialCycleResponse base g k E+Real.sqrt (cgEnergy base g k) • freshDefect base g E (k+1) := by
  have hs : canonicalCGStep base g k=Real.sqrt (cgEnergy base g k) • canonicalCGUnitStep base g k := by
    rw [cgEnergy_sqrt base hb]
    exact (NormedSpace.norm_smul_normalize _).symm
  unfold deferredResponse deferredTail partialCycleResponse freshDefect
  rw [Nat.add_sub_cancel,Finset.smul_sum,Finset.smul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro l _
  rw [map_add,map_smul,map_add,map_smul,hs,map_smul,map_smul]
  rfl

/-- Every original deferred response lies in the genuine strictly pre-final
explored flag for arbitrary matrix increments and damping values.
Use: its final true CG-step coordinate is zero, exactly as required by search.
Article: main_krylov, thm:DC.
Proof: both its genuine pre-final FC and fresh response components belong to
the same actual old explored flag, which is closed under real scaling and sums. -/
theorem deferred_response_mem (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (epsilon : ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    deferredResponse base g k epsilon E∈exploredFlag base g k := by
  rw [deferred_response_split base hb]
  apply (exploredFlag base g k).add_mem
  · exact (exploredFlag base g k).smul_mem _ (partialCycleResponse_mem base g k E)
  · apply (exploredFlag base g k).smul_mem
    simpa only [Nat.add_sub_cancel] using freshDefect_mem base g E (k+1)

/-- The true pre-final FC response coordinates are exactly its original
physical cumulative-defect staircase on the genuine CG steps.
Use: bridge the previously proved canonical response to actual old residual jets.
Article: main_krylov, thm:DC.
Proof: reuse the true prefix coordinates, actual cumulative increment
subtraction and genuine physical/canonical metric pairing term by term. -/
theorem partial_response_physical_coordinates (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hcount : k≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (i : ℕ) (hi : i<k) :
    (∑ j∈Ico (i+1) k,inner ℝ (referenceStep (cgOperator base) g i)
      ((cumulativeDrift base E j-cumulativeDrift base E i) (referenceStep (cgOperator base) g j)))=
      inner ℝ (canonicalCGStep base g i) (partialCycleResponse base g k E) := by
  rw [partialCycleResponse_coordinates base hb g hcount E hi]
  apply sum_congr rfl
  intro j hj
  rw [cumulativeDrift_sub base E (by have := (mem_Ico.mp hj).1;omega),metric_drift_pairing]
  rfl

/-- Each genuine old CG-step coordinate of the literal deferred response is
precisely the original damped FC staircase plus its true final fresh defect.
Use: identify the actual arbitrary-observed-estimate deferred first variation.
Article: main_krylov, thm:DC.
Proof: split the original response into its proved genuine pre-final and
fresh components, and apply both exact physical coordinate dictionaries. -/
theorem deferred_response_physical_coordinates (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g)
    (epsilon : ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (i : ℕ) (hi : i<k) :
    inner ℝ (canonicalCGStep base g i) (deferredResponse base g k epsilon E)=
      epsilon*(∑ j∈Ico (i+1) k,inner ℝ (referenceStep (cgOperator base) g i)
        ((cumulativeDrift base E j-cumulativeDrift base E i) (referenceStep (cgOperator base) g j)))+
      inner ℝ (referenceStep (cgOperator base) g i)
        ((cumulativeDrift base E k-cumulativeDrift base E i) (referenceStep (cgOperator base) g k)) := by
  rw [deferred_response_split base hb,inner_add_right,real_inner_smul_right,
    ← partial_response_physical_coordinates base hb g k (by omega) E i hi,
    ← freshDefect_physical_coordinates base hb g k hcount E i hi]

/-- The genuine last CG-step coordinate of the original deferred response is
exactly zero throughout every true active finite prefix.
Use: match the native final exact-search residual in full response reconstruction.
Article: main_krylov, thm:DC.
Proof: the entire actual response belongs to the strictly old explored flag,
which the genuine later CG step annihilates. -/
theorem deferred_response_last_coordinate (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hcount : k+1≤referenceAtomCount base hb g)
    (epsilon : ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    inner ℝ (canonicalCGStep base g k) (deferredResponse base g k epsilon E)=0 := by
  have horth := canonicalCGStep_later_orthogonal base hb g (k+1) k k hcount le_rfl (by omega)
  have hz := ((exploredFlag base g k).mem_orthogonal _).mp horth _ (deferred_response_mem base hb g k epsilon E)
  exact (real_inner_comm _ _).trans hz

end
end krylov.Cancellation
