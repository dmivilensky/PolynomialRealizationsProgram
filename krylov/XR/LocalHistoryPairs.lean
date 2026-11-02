import krylov.XR.LocalHistoryDictionary
import krylov.XR.LocalHistoryProgram

/-!
Article: main_krylov, lem:xr-local, exact endpoint-history transport.
Use: appending the true next endpoint to the smooth chart gives exactly
the native append-and-transport list update. Source: chronological finite
arrays and bilinearity of the actual transported anchor covectors.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine new record as a function of cached endpoint data and the
next actual value/gradient response. -/
def endpointNewObservation {k : ℕ} (C : EndpointChart E k) (point : E)
    (observation : ℝ × E) : PairObservation E where
  step := point - C.1 (Fin.last k)
  image := observation.2 - C.2.2 (Fin.last k)
  anchor := C.1 (Fin.last k)
  anchorPairing := 0
  valueDefect := observation.1 - C.2.1 (Fin.last k) -
    inner ℝ (C.2.2 (Fin.last k)) (point - C.1 (Fin.last k)) -
    inner ℝ (point - C.1 (Fin.last k)) (observation.2 - C.2.2 (Fin.last k)) / 2

/-- The endpoint chart's new full record list is exactly the actual native
append followed by the original anchor transport, including the new pair. -/
theorem endpointObservations_extend {k : ℕ} (C : EndpointChart E k) (point : E)
    (observation : ℝ × E) :
    endpointObservations (extendEndpointChart C point observation) =
      (endpointObservations C ++ [endpointNewObservation C point observation]).map
        (fun a => a.transport (point - C.1 (Fin.last k))) := by
  simp only [endpointObservations, List.ofFn_succ', List.map_append, List.map_cons, List.map_nil,
    List.map_ofFn, List.concat_eq_append]
  congr 1
  · apply congrArg List.ofFn
    funext i
    dsimp only [endpointStep, endpointImage, endpointDefect, extendEndpointChart,
      PairObservation.transport]
    simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, Function.comp_apply]
    congr 1
    rw [← inner_add_right]
    congr 1
    abel
  · simp only [extendEndpointChart, endpointStep, endpointImage, endpointDefect,
      endpointNewObservation, PairObservation.transport, Fin.snoc_last,
      Fin.snoc_castSucc, Fin.succ_last, zero_add]

end
end krylov.XR
