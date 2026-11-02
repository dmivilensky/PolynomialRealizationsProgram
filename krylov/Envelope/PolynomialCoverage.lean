import krylov.Envelope.AbsorbedPolynomialPairing
import krylov.Envelope.ScenarioRFC

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, actual polynomial coverage of the explored flag.
Use: represent every true common-tilt direction by the genuine source
polynomial vector, with its actual degree bound.
Source: actual CG polynomial Krylov flag and its real metric-root image.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.LinearAlgebra Polynomial Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual vector in the genuine explored canonical CG flag has a source polynomial representation of degree strictly below the horizon.
Use: Every actual vector in the genuine explored canonical CG flag has a source polynomial representation of degree strictly below the horizon.
Article: main_krylov, thm:select, actual polynomial coverage of the explored flag.
Proof: Unpack both actual submodule images, through the true metric root and the genuine degree-bounded polynomial action. Treat the zero polynomial with the positive horizon. -/
theorem canonicalPolynomialVector_covers (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 0<N) (hcount : N≤referenceAtomCount base hb g)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v∈exploredFlag base g N) :
    ∃ p : ℝ[X], p.natDegree<N ∧ canonicalPolynomialVector base g p=v := by
  -- Unpack the true metric-root Krylov image and its genuine low-degree polynomial representation.
  rw [exploredFlag_eq_primal_krylov base hb g N (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount))] at hv
  obtain ⟨w,hw,rfl⟩ := hv
  obtain ⟨p,hp,rfl⟩ := hw
  refine ⟨p,?_,rfl⟩
  by_cases hz : p=0
  · simpa only [hz,natDegree_zero] using hN
  · exact (natDegree_lt_iff_degree_lt hz).mpr ((mem_degreeLT).mp hp)

/-- The genuine continuous common-tilt operator takes values in the actual explored canonical CG flag.
Use: The genuine continuous common-tilt operator takes values in the actual explored canonical CG flag.
Article: main_krylov, thm:select, actual polynomial coverage of the explored flag.
Proof: Its actual definition is the negative explored orthogonal projection of a real RFC cycle derivative. -/
theorem canonicalTiltLinear_mem_flag (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (E : Fin (N-1) → Matrix (Fin n) (Fin n) ℝ) :
    canonicalTiltLinear base g N E∈exploredFlag base g N := by
  change -((exploredFlag base g N).starProjection _)∈_
  exact Submodule.neg_mem _ (Submodule.starProjection_apply_mem _ _)
end
end krylov.Envelope
