import chebyshev1.Algebra.OrderedProduct
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
Article: main_krylov, s6:kernel and prop:dict(i), actual fixed affine unrolling.
Use: solve real inhomogeneous fixed-memory recurrences with their genuine
independent injections before identifying scalar transfer polynomials.
Source: finite variation of constants; ordered products reuse the already
proved chronological convention of PasechnyukTakac26.
-/

namespace krylov.Realization
noncomputable section
open chebyshev1
open scoped BigOperators
variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- The actual state of a fixed affine linear recurrence with prescribed real injections.
Use: the additive input is the actual oracle injection, rather than a formal derivative symbol.
Article: main_krylov, s6:kernel, fixed affine recursion. -/
def affineRun (C : ℕ → F →ₗ[ℝ] F) (input : ℕ → F) (initial : F) : ℕ → F
  | 0 => initial
  | k+1 => C k (affineRun C input initial k)+input k

/-- The true inhomogeneous fixed-memory state equals its unperturbed transfer plus all actual injection tails.
Use: arbitrary fixed memory and arbitrary genuine independent injections are covered exactly, including an empty horizon.
Article: main_krylov, s6:kernel and prop:dict(i), exact affine unrolling.
Proof: induct over real recurrence updates. The current linear map propagates
the earlier actual injections, extending their genuine chronological tails;
the newest injection has the empty identity tail. -/
theorem affineRun_unroll (C : ℕ → F →ₗ[ℝ] F) (input : ℕ → F) (initial : F) (N : ℕ) :
    affineRun C input initial N=orderedProduct C N initial+
      ∑ s∈Finset.range N, orderedProduct (fun j => C (s+1+j)) (N-(s+1)) (input s) := by
  -- Tail lengths and indices are justified only for actual earlier injections s<N.
  induction N with
  | zero => simp only [affineRun,orderedProduct_zero,Module.End.one_apply,Finset.range_zero,Finset.sum_empty,add_zero]
  | succ N ih =>
    rw [affineRun,ih,map_add,map_sum,orderedProduct_succ,Finset.sum_range_succ]
    have htail (s : ℕ) (hs : s∈Finset.range N) :
        C N (orderedProduct (fun j => C (s+1+j)) (N-(s+1)) (input s))=
        orderedProduct (fun j => C (s+1+j)) (N+1-(s+1)) (input s) := by
      have hs' := Finset.mem_range.mp hs
      rw [show N+1-(s+1)=(N-(s+1))+1 by omega,orderedProduct_succ]
      have he : s+1+(N-(s+1))=N := by omega
      rw [he]
      rfl
    simp only [show N+1-(N+1)=0 by omega,orderedProduct_zero,Module.End.one_apply]
    rw [Finset.sum_congr rfl htail]
    exact add_assoc _ _ _

/-- Every actual linear readout of the fixed-memory run has the exact same genuine independent-injection decomposition.
Use: apply to the physical error, queried error or any output coordinate of an oblivious realization.
Article: main_krylov, s6:kernel, actual terminal error formula.
Proof: apply the actual linear readout to the proved full state identity and distribute over its finite sum. -/
theorem affineRun_readout {V : Type*} [AddCommGroup V] [Module ℝ V]
    (C : ℕ → F →ₗ[ℝ] F) (input : ℕ → F) (initial : F) (readout : F →ₗ[ℝ] V) (N : ℕ) :
    readout (affineRun C input initial N)=readout (orderedProduct C N initial)+
      ∑ s∈Finset.range N, readout (orderedProduct (fun j => C (s+1+j)) (N-(s+1)) (input s)) := by
  rw [affineRun_unroll,map_add,map_sum]

end
end krylov.Realization
