import krylov.Methods.HistoryMap
import krylov.Methods.ObservedRules

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, genuine fixed coefficient-history synthesis.
Use: express every real reconstructed observation as an actual finite
linear combination of the original genuine input data, using one true
fixed history of standard coordinate coefficients for each query shape.
Source: actual finite scalar-vector synthesis, the standard coordinate
unit family and proved genuine linear observed-history reconstruction.
-/

namespace krylov.Methods
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

/-- The true finite linear synthesis map from genuine scalar observation coefficients to actual observed vectors.
Use: The true finite linear synthesis map from genuine scalar observation coefficients to actual observed vectors.
Article: main_krylov, def:classes and cor:lm, genuine fixed coefficient-history synthesis.
Proof: Use the actual finite scalar-vector combination with its genuine linearity. -/
def observationSynthesis (data : Fin m → E) : (Fin m → ℝ) →ₗ[ℝ] E where
  toFun := combine data
  map_add' a b := by simp only [combine,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a b := by
    simp only [combine,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.smul_sum,smul_smul]

/-- Each true coordinate unit synthesizes exactly its actual observed vector.
Use: Each true coordinate unit synthesizes exactly its actual observed vector.
Article: main_krylov, def:classes and cor:lm, genuine fixed coefficient-history synthesis.
Proof: The genuine finite coordinate-unit sum has exactly its real selected term. -/
theorem observationSynthesis_single (data : Fin m → E) (i : Fin m) :
    observationSynthesis data (Pi.single i 1)=data i := by
  change combine data (Pi.single i 1)=data i
  simp [combine,Pi.single_apply]

/-- The genuine fixed coefficient-valued complete history for a true discrete observation shape.
Use: The genuine fixed coefficient-valued complete history for a true discrete observation shape.
Article: main_krylov, def:classes and cor:lm, genuine fixed coefficient-history synthesis.
Proof: Reconstruct the actual record/query layout on the standard finite scalar coordinate vectors. -/
def coefficientHistory (shape : List ℕ) (m : ℕ) : History (Fin m → ℝ) :=
  historyFromObservations shape (List.ofFn fun i : Fin m => (Pi.single i 1 : Fin m → ℝ))

/-- Every actual reconstructed complete history is exactly the real linear synthesis image of its genuine fixed coefficient history.
Use: Every actual reconstructed complete history is exactly the real linear synthesis image of its genuine fixed coefficient history.
Article: main_krylov, def:classes and cor:lm, genuine fixed coefficient-history synthesis.
Proof: The true observation synthesis maps every genuine coordinate unit to its real input vector; apply the proved actual linear reconstruction identity to that exact finite observation list. -/
theorem coefficientHistory_synthesis (shape : List ℕ) (data : Fin m → E) :
    (coefficientHistory shape m).map (observationSynthesis data)=
      historyFromObservations shape (List.ofFn data) := by
  -- Synthesize the genuine coordinate-unit observations before invoking actual complete-history reconstruction.
  unfold coefficientHistory
  rw [← historyFromObservations_map (observationSynthesis data) (map_zero _) ]
  have hl : (List.ofFn fun i : Fin m => (Pi.single i 1 : Fin m → ℝ)).map (observationSynthesis data)=List.ofFn data := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact observationSynthesis_single data i
  rw [hl]
end
end krylov.Methods
