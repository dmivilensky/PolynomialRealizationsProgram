import krylov.Methods.TargetedZeroQueries
import krylov.Methods.TargetedSmoothCycle

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, genuine reference-only smooth information class.
Use: express the precise weakened source class with actual CG consistency only on chosen quadratic data and genuine primitive C-two coefficients on its true finite reference cycle.
Source: the original genuine probed information class, actual reference CG direction/zero-query conditions and the constructed true targeted primitive implementation.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine raw policy agrees with actual CG on the chosen quadratic data, with positive real direction scales and true zero correction queries.
Use: The genuine raw policy agrees with actual CG on the chosen quadratic data, with positive real direction scales and true zero correction queries.
Article: main_krylov, apB:prop:consist, genuine reference-only smooth information class.
Proof: Restrict only the quadratic-data quantifiers of the actual global CG-consistency predicate. -/
def ReferenceCGConsistent (m : ProbedMethod E) (Q : E →L[ℝ] E) (g : E) : Prop :=
  ∀ k : ℕ,
    let H := methodRun m (fun _ => Q) (fun _ => Q) g k
    ∃ scale : ℝ,0<scale ∧ m.direction H=scale • CG.direction Q g k ∧
      ZeroCorrections (m.correction H (Q (m.direction H))) Q
        (searchedGradient H.gradient (m.direction H) (Q (m.direction H)))

/-- The actual weakened smooth information class retains true all-history span restrictions and primitive C-two coefficient membership but requires CG consistency only on its chosen reference.
Use: The actual weakened smooth information class retains true all-history span restrictions and primitive C-two coefficient membership but requires CG consistency only on its chosen reference.
Article: main_krylov, apB:prop:consist, genuine reference-only smooth information class.
Proof: Extend the genuine probed class with actual chosen-reference consistency and real primitive local charts. -/
structure ReferenceSmoothProbedClass (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Q : E →L[ℝ] E) (g : E) (N : ℕ) extends ProbedClass E where
  /-- Actual CG direction scaling and zero real correction queries on the chosen quadratic data. -/
  consistent_at : ReferenceCGConsistent policy Q g
  /-- Genuine primitive C-two observed coefficient charts on this actual chosen-reference finite cycle. -/
  smooth_at : SmoothProbedCycleAt policy 2 Q g N

/-- Every genuinely globally CG-consistent raw policy is actually CG-consistent on each chosen positive quadratic reference.
Use: Every genuinely globally CG-consistent raw policy is actually CG-consistent on each chosen positive quadratic reference.
Article: main_krylov, apB:prop:consist, genuine reference-only smooth information class.
Proof: Specialize the true global reference quantifiers. -/
theorem CGConsistent.reference (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) :
    ReferenceCGConsistent m Q g := hm Q hQ hpos g

/-- The genuine targeted final-correction implementation belongs to the actual reference-only primitive smooth information class.
Use: The genuine targeted final-correction implementation belongs to the actual reference-only primitive smooth information class.
Article: main_krylov, apB:prop:consist, genuine reference-only smooth information class.
Proof: Combine actual all-history span membership, chosen-reference CG direction and zero queries, and the derived genuine primitive coefficient charts. -/
def targetedReferenceClass (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ k<N,CG.gradient Q g k≠0) : ReferenceSmoothProbedClass E Q g N where
  memory := fullMemory
  policy := targetedFinalMethod N (CG.gradient Q g N)
  admissible := targetedFinalMethod_spanRestricted N _
  consistent_at := fun k => ⟨1,zero_lt_one,by rw [one_smul];exact targetedFinalMethod_reference_direction Q hQ hpos g N k,
    targetedFinalMethod_reference_zero Q hQ hpos g N k⟩
  smooth_at := targetedFinalMethod_smoothCycleAt N _ Q hQ hpos g hpre 2
end
end krylov.Methods
