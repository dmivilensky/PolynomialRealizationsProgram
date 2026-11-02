import krylov.XR.EuclideanModel
import krylov.XR.MemoryRank
import krylov.XR.MemoryObservations

/-!
Article: main_krylov, cor:xrF, unchanged observed-window selection.
Use: retain the original rank/deletion/source bookkeeping for the actual
Euclidean split option. Source: the two models have definitionally identical
retained pairs; only their computed correction matrices differ.
-/
namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant
open scoped InnerProductSpace
variable {n : ℕ}

/-- Euclidean correction leaves the original full column-rank cleanup intact. -/
theorem euclideanAlgorithmModel_independent (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    LinearIndependent ℝ (storedSteps (euclideanAlgorithmModel P S).pairs):=algorithmModel_independent P S

/-- The Euclidean option obeys the original capacity and dimension bound. -/
theorem euclideanAlgorithmModel_length_le (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) :
    (euclideanAlgorithmModel P S).pairs.length≤min S.capacity n:=algorithmModel_length_le P S

/-- No pair is invented by the Euclidean variant's unchanged selection. -/
theorem euclideanAlgorithmModel_pair_mem (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n)))
    (a : PairObservation (EuclideanSpace ℝ (Fin n))) (ha : a∈(euclideanAlgorithmModel P S).pairs) :
    a∈S.pairs:=algorithmModel_pair_mem P S a ha

end
end krylov.XR
