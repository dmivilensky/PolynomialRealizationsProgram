import krylov.Correction.DeepStage0

/-!
Article: main_krylov, prop:deep, exact dyadic singular-model interval.
Use: Fix the two original nearby exact rational parameters, their true
ordering and independently checked interval/endpoint input enclosures.
Source: printed rational RFC family; exact rational ordering and unchanged
earlier-package rational interval checker soundness.
-/

namespace krylov.Correction.Certificate
noncomputable section
open chebyshev2.Numerics.IntegerCertificate
/-- The exact dyadic left parameter of the original final-model determinant sign change.
Use: Apply the actual source certificate on the original interval and at its genuine endpoints.
Article: main_krylov, prop:deep, exact original parameter interval.
-/
def deepLeft : ℚ := 2646454928180481456171251146847918056121676983675537773643408674368639160074972432041573143760250154588367653162907394362391485/2707685248164858261307045101702230179137145581421695874189921465443966120903931272499975005961073806735733604454495675614232576
/-- The immediately succeeding exact dyadic right parameter of the original sign change.
Use: Apply the actual source certificate on the original interval and at its genuine endpoints.
Article: main_krylov, prop:deep, exact original parameter interval.
-/
def deepRight : ℚ := 1323227464090240728085625573423959028060838491837768886821704337184319580037486216020786571880125077294183826581453697181195743/1353842624082429130653522550851115089568572790710847937094960732721983060451965636249987502980536903367866802227247837807116288

/-- The true two dyadic endpoints lie strictly ordered inside the original affine source domain.
Use: Apply the actual source certificate on the original interval and at its genuine endpoints.
Article: main_krylov, prop:deep, exact original parameter interval.
Proof: Use exact rational arithmetic and the unchanged rational interval checker soundness theorem.
-/
theorem deep_endpoints : 0<(deepLeft : ℝ) ∧ (deepLeft : ℝ)<deepRight ∧ (deepRight : ℝ)<1 := by
  have h : 0<deepLeft ∧ deepLeft<deepRight ∧ deepRight<1 := by decide +kernel
  exact_mod_cast h

/-- The true left rational endpoint of the whole-interval or singleton-endpoint certificate domain.
Use: Apply the actual source certificate on the original interval and at its genuine endpoints.
Article: main_krylov, prop:deep, exact original parameter interval.
-/
def deepDomainLeft (d : Fin 3) : ℚ := if d=2 then deepRight else deepLeft
/-- The true right rational endpoint of the whole-interval or singleton-endpoint certificate domain.
Use: Apply the actual source certificate on the original interval and at its genuine endpoints.
Article: main_krylov, prop:deep, exact original parameter interval.
-/
def deepDomainRight (d : Fin 3) : ℚ := if d=1 then deepLeft else deepRight

/-- The exact original integer parameter interval proposed for each source certificate domain.
Use: Apply the actual source certificate on the original interval and at its genuine endpoints.
Article: main_krylov, prop:deep, exact original parameter interval.
-/
def deepParameterBounds (d : Fin 3) : Bounds :=
  if d=0 then deepStage0IntervalInputs.getD 0 ⟨0,0⟩
  else if d=1 then deepStage0LeftInputs.getD 0 ⟨0,0⟩
  else deepStage0RightInputs.getD 0 ⟨0,0⟩

/-- The unchanged exact rational interval checker accepts both true endpoints of each original source domain.
Use: Apply the actual source certificate on the original interval and at its genuine endpoints.
Article: main_krylov, prop:deep, exact original parameter interval.
Proof: Use exact rational arithmetic and the unchanged rational interval checker soundness theorem.
-/
theorem deep_parameter_checked (d : Fin 3) :
    rationalIntervalCheck deepScale (deepDomainLeft d) (deepDomainRight d) (deepParameterBounds d)=true := by
  fin_cases d <;> decide +kernel

/-- Every actual parameter in its original source domain has the independently checked exact input enclosure.
Use: Apply the actual source certificate on the original interval and at its genuine endpoints.
Article: main_krylov, prop:deep, exact original parameter interval.
Proof: Use exact rational arithmetic and the unchanged rational interval checker soundness theorem.
-/
theorem deep_parameter_enclosed (d : Fin 3) {s : ℝ}
    (hs : s∈Set.Icc (deepDomainLeft d : ℝ) (deepDomainRight d : ℝ)) :
    (deepParameterBounds d).Mem deepScale s :=
  rationalIntervalCheck_sound deepScale_pos (deep_parameter_checked d) hs.1 hs.2

end
end krylov.Correction.Certificate
