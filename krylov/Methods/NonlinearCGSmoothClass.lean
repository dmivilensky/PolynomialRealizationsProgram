import krylov.Methods.EmptyCompilation
import krylov.Methods.NonlinearCGCharts

set_option autoImplicit false
/-!
Article: main_krylov, cor:lm and s3:cor:qn, genuine smooth HS/HZ source-class bridges.
Use: prove full primitive smooth information-class membership of the
actual Hestenes--Stiefel and Hager--Zhang implementations.
Source: HestenesStiefel52 and HagerZhang05; actual quadratic transcripts,
positive observed reference denominators and concrete finite primitive coefficients.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual newest nonlinear CG reference record has the true current and preceding CG gradients and genuine preceding CG direction.
Use: The actual newest nonlinear CG reference record has the true current and preceding CG gradients and genuine preceding CG direction.
Article: main_krylov, cor:lm and s3:cor:qn, genuine smooth HS/HZ source-class bridges.
Proof: Use the actual static transcript at consecutive real iteration indices; the genuine empty correction preserves the true previous history. -/
theorem nonlinearCG_reference_history (coefficient : E → E → E → ℝ)
    (Q : E →L[ℝ] E) (g : E)
    (hcoef : ∀ k, coefficient (CG.gradient Q g (k+1)) (CG.gradient Q g k)
      (CG.direction Q g k)=CG.beta Q g k) (k : ℕ) :
    let H := methodRun (nonlinearCGMethod coefficient) (fun _ => Q) (fun _ => Q) g (k+1)
    H.gradient=CG.gradient Q g (k+1) ∧ (historyTail H).gradient=CG.gradient Q g k ∧
      historyLastDirection H=CG.direction Q g k := by
  have hs := nonlinearCGMethod_static coefficient Q g hcoef k
  have hn := nonlinearCGMethod_static coefficient Q g hcoef (k+1)
  exact ⟨hn.1,hs.1,hs.2⟩

/-- An actual nonlinear CG scalar rule with its genuine finite primitive coefficient domains has a true smooth primitive representation on every active quadratic cycle.
Use: An actual nonlinear CG scalar rule with its genuine finite primitive coefficient domains has a true smooth primitive representation on every active quadratic cycle.
Article: main_krylov, cor:lm and s3:cor:qn, genuine smooth HS/HZ source-class bridges.
Proof: Compile the actual finite observed direction rule and true empty corrections. Recover genuine quadratic history fields and derive the real nonzero primitive denominator from actual CG positivity. -/
theorem nonlinearCG_smoothCycleAt (coefficient : E → E → E → ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hcoef : ∀ k, coefficient (CG.gradient Q g (k+1)) (CG.gradient Q g k)
      (CG.direction Q g k)=CG.beta Q g k)
    (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0) (r : WithTop ℕ∞)
    (hprimitive : ∀ (shape : List ℕ) (n : ℕ) (data : Fin n → E),
      (shape≠[] → let H := historyFromObservations shape (List.ofFn data)
        inner ℝ (historyLastDirection H) (H.gradient-(historyTail H).gradient)≠0) →
      ContDiffAt ℝ r (nonlinearCGObservedRule coefficient shape n).coefficient data) :
    SmoothProbedCycleAt (nonlinearCGMethod coefficient) r Q g N := by
  -- Compile the true finite observed rule, then derive its actual scalar inverse domain from the genuine consecutive quadratic history fields.
  apply emptyCompiled_smoothCycleAt (nonlinearCGMethod coefficient) (fun _ _ => rfl)
    (nonlinearCGObservedRule coefficient) (nonlinearCGObservedRule_evaluate coefficient) Q g N r
  intro k hk
  apply hprimitive
  intro _
  rw [ofFn_observedArray,historyFromObservations_actual]
  cases k with
  | zero => contradiction
  | succ k =>
    have hs := nonlinearCG_reference_history coefficient Q g hcoef k
    dsimp only at hs
    dsimp only
    rw [hs.1,hs.2.1,hs.2.2]
    exact (nonlinearCG_reference_denominator Q hQ hpos g k (hpre k (by omega))).ne'

/-- The actual Hestenes--Stiefel method has genuine primitive smooth-cycle membership at every order on every true active positive quadratic reference.
Use: The actual Hestenes--Stiefel method has genuine primitive smooth-cycle membership at every order on every true active positive quadratic reference.
Article: main_krylov, cor:lm and s3:cor:qn, genuine smooth HS/HZ source-class bridges.
Proof: Use its actual CG coefficient identity and the proved genuine observed coefficient regularity on the derived positive reference denominator. -/
theorem hsMethod_smoothCycleAt (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0) (r : WithTop ℕ∞) :
    SmoothProbedCycleAt (nonlinearCGMethod hsCoefficient) r Q g N :=
  nonlinearCG_smoothCycleAt hsCoefficient Q hQ hpos g
    (fun k => (nonlinear_cg_coefficients Q hQ hpos g k).1) N hpre r
    (fun _ _ _ hd => hsObservedRule_regular _ _ hd)

/-- The actual Hager--Zhang method has genuine primitive smooth-cycle membership at every order on every true active positive quadratic reference.
Use: The actual Hager--Zhang method has genuine primitive smooth-cycle membership at every order on every true active positive quadratic reference.
Article: main_krylov, cor:lm and s3:cor:qn, genuine smooth HS/HZ source-class bridges.
Proof: Use its actual CG coefficient identity and true finite observed primitive coefficient regularity on the genuine positive reference denominator. -/
theorem hzMethod_smoothCycleAt (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0) (r : WithTop ℕ∞) :
    SmoothProbedCycleAt (nonlinearCGMethod hzCoefficient) r Q g N :=
  nonlinearCG_smoothCycleAt hzCoefficient Q hQ hpos g
    (fun k => (nonlinear_cg_coefficients Q hQ hpos g k).2) N hpre r
    (fun _ _ _ hd => hzObservedRule_regular _ _ hd)

/-- The actual Hestenes--Stiefel policy as a genuine smooth globally CG-consistent source information-class member.
Use: The actual Hestenes--Stiefel policy as a genuine smooth globally CG-consistent source information-class member.
Article: main_krylov, cor:lm and s3:cor:qn, genuine smooth HS/HZ source-class bridges.
Proof: Combine its true all-history observed-span admissibility, actual global quadratic consistency and genuine primitive smooth local representation. -/
def smoothHSClass : SmoothProbedClass E where
  memory := fullMemory
  policy := nonlinearCGMethod hsCoefficient
  admissible := nonlinearCGMethod_spanRestricted hsCoefficient fullMemory
  consistent := hsMethod_consistent
  smooth := fun Q hQ hpos g N hpre => hsMethod_smoothCycleAt Q hQ hpos g N hpre 2

/-- The actual Hager--Zhang policy as a genuine smooth globally CG-consistent source information-class member.
Use: The actual Hager--Zhang policy as a genuine smooth globally CG-consistent source information-class member.
Article: main_krylov, cor:lm and s3:cor:qn, genuine smooth HS/HZ source-class bridges.
Proof: Combine the actual observed-span policy, proved true global CG consistency and genuine finite primitive coefficient representation. -/
def smoothHZClass : SmoothProbedClass E where
  memory := fullMemory
  policy := nonlinearCGMethod hzCoefficient
  admissible := nonlinearCGMethod_spanRestricted hzCoefficient fullMemory
  consistent := hzMethod_consistent
  smooth := fun Q hQ hpos g N hpre => hzMethod_smoothCycleAt Q hQ hpos g N hpre 2
end
end krylov.Methods
