import krylov.Envelope.CanonicalShadow
import krylov.Envelope.StaticPolynomialVariation

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:DK, actual absorbed common-tilt polynomial sensitivity.
Use: identify the genuine common-tilt functional on actual Krylov
polynomial vectors with the true ordered noncommutative quadratic
CG sensitivity, as the real precursor of the printed Daleckii--Krein matrix.
Source: DaleckiiKrein65 for standard sensitivity attribution; actual
differentiated CG Galerkin identity and constructed genuine absorbed information fibre.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Polynomial Matrix
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine source canonical polynomial Krylov vector A to the one-half times the actual polynomial action on the true initial gradient.
Use: The genuine source canonical polynomial Krylov vector A to the one-half times the actual polynomial action on the true initial gradient.
Article: main_krylov, apB:lem:DK, actual absorbed common-tilt polynomial sensitivity.
Proof: Apply the real reference metric root to the genuine operator-polynomial vector. -/
def canonicalPolynomialVector (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (p : ℝ[X]) : EuclideanSpace ℝ (Fin n) := cgOperator (metricRoot base) ((aeval (cgOperator base) p) g)

/-- Every true degree-admissible canonical polynomial vector lies in the genuine actual explored CG flag.
Use: Every true degree-admissible canonical polynomial vector lies in the genuine actual explored CG flag.
Article: main_krylov, apB:lem:DK, actual absorbed common-tilt polynomial sensitivity.
Proof: The genuine polynomial action belongs to its true physical Krylov flag, whose real metric-root image is the actual explored canonical flag. -/
theorem canonicalPolynomialVector_mem (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (p : ℝ[X]) (hdegree : p.natDegree<N) : canonicalPolynomialVector base g p∈exploredFlag base g N := by
  rw [exploredFlag_eq_primal_krylov base hb g N (fun i hi => cg_nonstagnation base hb g i (hi.trans_le hcount))]
  exact Submodule.mem_map_of_mem (polynomialAction_mem_krylov (cgOperator base) g N p hdegree)

/-- Pairing a genuine canonical polynomial flag vector with the actual explored inverse-root projection gives exactly its true physical polynomial-gradient pairing.
Use: Pairing a genuine canonical polynomial flag vector with the actual explored inverse-root projection gives exactly its true physical polynomial-gradient pairing.
Article: main_krylov, apB:lem:DK, actual absorbed common-tilt polynomial sensitivity.
Proof: The actual explored projection fixes the true polynomial flag vector; the genuine root/inverse-root metric pairing then cancels both real factors. -/
theorem canonicalPolynomialVector_projection_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (p : ℝ[X]) (hdegree : p.natDegree<N) (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (canonicalPolynomialVector base g p) ((exploredFlag base g N).starProjection (cgOperator (metricRoot base)⁻¹ v))=
      inner ℝ ((aeval (cgOperator base) p) g) v := by
  let P := exploredFlag base g N
  have hp : P.starProjection (canonicalPolynomialVector base g p)=canonicalPolynomialVector base g p :=
    Submodule.starProjection_eq_self_iff.mpr (canonicalPolynomialVector_mem base hb g N hcount p hdegree)
  rw [← P.inner_starProjection_left_eq_right,hp]
  exact (canonical_search_pairing base hb ((aeval (cgOperator base) p) g) v).symm

/-- On actual symmetric absorbed canonical scenarios the genuine common-tilt polynomial functional equals the true ordered operator-polynomial sensitivity pairing with the actual reference CG gradient.
Use: On actual symmetric absorbed canonical scenarios the genuine common-tilt polynomial functional equals the true ordered operator-polynomial sensitivity pairing with the actual reference CG gradient.
Article: main_krylov, apB:lem:DK, actual absorbed common-tilt polynomial sensitivity.
Proof: Construct the genuine positive single-quadratic shadow and differentiate its actual Galerkin identity. The true RFC derivative is exactly the real shadow CG derivative, and genuine RFC residual cancellation identifies its actual explored component with minus the common tilt. True canonical metric pairing gives the claimed real scalar identity. -/
theorem absorbed_tilt_polynomial_pairing (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l<N-1, (E l).IsSymm) (habs : AbsorbedIncrements base g E N)
    (p : ℝ[X]) (hdegree : p.natDegree<N) :
    inner ℝ (canonicalPolynomialVector base g p) (commonTilt base g (canonicalFCPath base E) N)=
      inner ℝ ((polynomialFirstVariation p (cgOperator base)
        (cgOperator (∑ l∈Finset.range (N-1),physicalIncrements base E l))) g) (CG.gradient (cgOperator base) g N) := by
  -- The genuine positive shadow supplies actual quadratic Galerkin sensitivity, while true RFC membership and residual cancellation identify the real common-tilt functional.
  let A := canonicalFCPath base E
  let D := ∑ l∈Finset.range (N-1),physicalIncrements base E l
  let T := positiveReferenceOperator base D
  have h0 : T 0=cgOperator base := positiveReferenceOperator_zero _ _
  have hsym : D.IsSymm := by
    change (∑ l∈Finset.range (N-1),physicalIncrements base E l)ᵀ=∑ l∈Finset.range (N-1),physicalIncrements base E l
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl (fun l hl => (physicalIncrements_symm base E l (hE l (Finset.mem_range.mp hl))).eq)
  have hpre (i : ℕ) (hi : i<N) : CG.gradient (cgOperator base) g i≠0 := cg_nonstagnation base hb g i (hi.trans_le hcount)
  have hr := rfcMethod_consistent fullMemory (fun _ hk => hk) 1 (E := EuclideanSpace ℝ (Fin n))
  have hs := rfcMethod_smoothCycleAt fullMemory 1 (cgOperator base) (cgOperator_positive base hb).1
    (cgOperator_positive base hb).2 g (fun _ _ hk => hk) N hpre 2
  have hj := actual_absorbed_canonical_gradient (rfcMethod fullMemory 1) hr base hb g N hcount hs E hE habs A
    (canonicalFCPath_zero base E) (fun i _ => (canonicalFCPath_calculus base E i).1.differentiableAt)
  have hCG := staticCG_polynomial_variation T (cgOperator D) g N (positiveReferenceOperator_analytic base D 0)
    (positiveReferenceOperator_hasDeriv base D) (by rw [h0];exact (cgOperator_positive base hb).1)
    (by rw [h0];exact (cgOperator_positive base hb).2) (by rw [h0];exact hpre)
    (positiveReferenceOperator_eventually_active base D hb hsym g N hpre) p hdegree
  rw [h0,← hj] at hCG
  have hν := fullRFC_tilt 1 (by norm_num) base hb g A A (fun i => (canonicalFCPath_calculus base E i).1)
    (fun i => (canonicalFCPath_calculus base E i).1) (canonicalFCPath_zero base E) (canonicalFCPath_zero base E) N hN hcount
  have hp := canonicalPolynomialVector_projection_pairing base hb g N hcount p hdegree
    (deriv (fun t => probedGradient (rfcMethod fullMemory 1) (A t) (A t) g N) 0)
  change (exploredFlag base g N).starProjection (cgOperator (metricRoot base)⁻¹
    (deriv (fun t => probedGradient (rfcMethod fullMemory 1) (A t) (A t) g N) 0))=_ at hν
  rw [hν,inner_neg_right] at hp
  change inner ℝ ((polynomialFirstVariation p (cgOperator base) (cgOperator D)) g) (CG.gradient (cgOperator base) g N)+
    inner ℝ ((aeval (cgOperator base) p) g) (deriv (fun t => probedGradient (rfcMethod fullMemory 1) (A t) (A t) g N) 0)=0 at hCG
  rw [← hp] at hCG
  linarith
end
end krylov.Envelope
