import krylov.Methods.ProjectedModel
import krylov.Methods.CorrectionCount
import krylov.Methods.InformationSpan
import krylov.LinearAlgebra.SpectralConditioning

/-!
Article: Definition 3.4 [def:GRFC] of krylov.tex.
Use: construct an actual nonanticipating method with FC fallback and prove
the inverse bound supplied by its spectral test, independently of later uniform estimates.
Source: the existing RFC executor, real diagonal normalization and the proved
finite symmetric spectral inverse estimate. The eigenvalue test means every
eigenvalue is at least γ, equivalently the minimum eigenvalue is at least γ.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual observed diagonal normalization of the latest-information model.
Use: the spectral test uses measured energies rather than unknown physical step norms.
Article: main_krylov, def:GRFC, Ĥ=diag(H)^(−1/2)Hdiag(H)^(−1/2). -/
def observedNormalizedModel (W : List (E × E)) : Matrix (Fin W.length) (Fin W.length) ℝ :=
  rescaleModel (windowModel W) (fun i => (Real.sqrt (windowModel W i i))⁻¹)

/-- The actual diagonally normalized observed model remains Hermitian.
Use: its true eigenvalues and the spectral inverse bound have their symmetry premise proved.
Article: main_krylov, def:GRFC, symmetry of Ĥ.
Proof: diagonal real normalization is a symmetric congruence of the symmetric latest model. -/
theorem observedNormalizedModel_hermitian (W : List (E × E)) :
    (observedNormalizedModel W).IsHermitian := by
  apply Matrix.isHermitian_iff_isSymm.mpr
  simp only [observedNormalizedModel,rescaleModel,Matrix.IsSymm,transpose_mul,
    diagonal_transpose,(windowModel_symmetric W).eq,Matrix.mul_assoc]

/-- The spectral acceptance test on actual positive observed energies.
Use: augment the existing observed-defect RFC gate without exposing any unknown operator.
Article: main_krylov, def:GRFC, positive diagonal and λ_min(Ĥ)≥γ_g. -/
def spectralGate (gamma : ℝ) (W : List (E × E)) : Prop :=
  (∀ i, 0 < windowModel W i i) ∧
    ∀ i, gamma ≤ (observedNormalizedModel_hermitian W).eigenvalues i

/-- Passing the spectral test proves invertibility and a uniform inverse bound for the actual normalized model.
Use: the accepted correction cannot hide a nearly singular normalized model.
Article: main_krylov, thm:UCg, ‖Ĥ⁻¹‖≤γ_g⁻¹.
Proof: apply the already proved genuine spectral inverse theorem to the measured model. -/
theorem spectralGate_inverse {gamma : ℝ} (hg : 0 < gamma) (W : List (E × E))
    (hgate : spectralGate gamma W) :
    IsUnit (observedNormalizedModel W).det ∧ ‖(observedNormalizedModel W)⁻¹‖ ≤ gamma⁻¹ :=
  inverse_bound_of_eigenvalues _ (observedNormalizedModel_hermitian W) hg hgate.2

/-- A passed spectral gate also proves that the actual unnormalized coefficient solve is nonsingular.
Use: justify the real executed RFC inverse before applying any correction identity.
Article: main_krylov, def:GRFC, well-defined accepted model solve.
Proof: the normalized determinant is a product containing the raw model determinant;
its proved nonzero value excludes a zero raw determinant. -/
theorem spectralGate_model_unit {gamma : ℝ} (hg : 0 < gamma) (W : List (E × E))
    (hgate : spectralGate gamma W) : IsUnit (windowModel W).det := by
  have hn := (spectralGate_inverse hg W hgate).1
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have he : (observedNormalizedModel W).det=0 := by
    simp only [observedNormalizedModel,rescaleModel,det_mul,hz,mul_zero,zero_mul]
  exact (isUnit_iff_ne_zero.mp hn) he

/-- The actual spectral-gated RFC correction rule with one real correction query.
Use: a failed spectral test returns the FC branch; the existing RFC rule supplies
the observed defect test, nonempty-window condition and actual correction solve.
Article: main_krylov, def:GRFC, gated RFC with FC fallback. -/
def gatedCorrection (memory : ℕ → ℕ) (gamma : ℝ) (H : History E) (z : E) : CorrectionTree E := by
  classical
  exact
    let W := selectedWindow memory H
    let d := windowDirection W H.gradient
    if spectralGate gamma ((d,z)::W) then rfcCorrection memory 1 H z else .done

/-- The actual data-only spectral-gated RFC method.
Use: run it through the same genuine probe, line-search and correction executor as ordinary RFC.
Article: main_krylov, def:GRFC, M_GRFC. -/
def gatedMethod (memory : ℕ → ℕ) (gamma : ℝ) : ProbedMethod E :=
  retainedMethod memory (gatedCorrection memory gamma)

/-- The spectral-gated method makes at most one actual correction per iteration.
Use: membership in the source's one-correction probed information class is proved.
Article: main_krylov, thm:C and def:GRFC, M_CG^(1).
Proof: a rejected spectral branch stops; the accepted branch is the proved actual one-correction RFC tree. -/
theorem gatedMethod_oneCorrection (memory : ℕ → ℕ) (gamma : ℝ) :
    OneCorrectionMethod (gatedMethod memory gamma : ProbedMethod E) := by
  intro H z
  change CorrectionsAtMostOne (gatedCorrection memory gamma H z)
  unfold gatedCorrection
  dsimp only
  split
  · exact rfcMethod_oneCorrection memory H z
  · trivial

/-- The actual gated method obeys the source's observed-direction and stored-correction-span restrictions.
Use: gate tests do not enlarge the information or query subspaces of the real method.
Article: main_krylov, def:classes and def:GRFC, admissible data-only policy.
Proof: the direction is the same observed retained solve; the correction either
stops or is precisely the already proved span-restricted RFC correction. -/
theorem gatedMethod_spanRestricted (memory : ℕ → ℕ) (gamma : ℝ) :
    ProbedSpanRestricted memory (gatedMethod memory gamma : ProbedMethod E) := by
  -- The extra spectral test selects between two already admissible query-span branches.
  intro H
  refine ⟨retained_direction_mem_observedSpan memory H,?_⟩
  intro z
  change (gatedCorrection memory gamma H z).InSubspace _
  unfold gatedCorrection
  dsimp only
  split
  · exact (rfcMethod_spanRestricted memory 1 H).2 z
  · trivial

/-- Every gated quadratic correction phase vanishes on the genuine CG transcript.
Use: derive quadratic consistency for the actual gated policy without assuming gate acceptance.
Article: main_krylov, def:GRFC and lem:consistent, zero reference corrections.
Proof: rejection stops immediately; acceptance uses the existing RFC quadratic
correction theorem on the same actual direction and measured probe. -/
theorem gatedCorrection_reference (memory : ℕ → ℕ) (gamma : ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (H : History E)
    (hg : H.gradient=CG.gradient Q g k) (hp : H.pairs=referencePairs Q g k)
    (hm : CG.gradient Q g k≠0 → 0<k → 0<memory k) :
    ZeroCorrections (gatedCorrection memory gamma H
      (Q ((gatedMethod memory gamma).direction H))) Q
      (searchedGradient H.gradient ((gatedMethod memory gamma).direction H)
        (Q ((gatedMethod memory gamma).direction H))) := by
  unfold gatedCorrection
  dsimp only
  split
  · exact rfcCorrection_reference memory 1 Q hQ hpos g k H hg hp hm
  · trivial

/-- The actual spectral-gated run has the genuine CG gradients and pairs on every static positive quadratic.
Use: the new implementation has a proved reference execution, including stopped tails.
Article: main_krylov, def:GRFC and lem:consistent, quadratic reference run.
Proof: the shared retained-policy induction uses the proved zero gated corrections at each actual history. -/
theorem gatedMethod_static (memory : ℕ → ℕ) (gamma : ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<memory k) (k : ℕ) :
    let H := methodRun (gatedMethod memory gamma) (fun _ => Q) (fun _ => Q) g k
    H.gradient=CG.gradient Q g k ∧ H.pairs=referencePairs Q g k :=
  retainedMethod_static memory _ Q hQ hpos g hm
    (fun j H hg hp => gatedCorrection_reference memory gamma Q hQ hpos g j H hg hp (hm j)) k

/-- The actual spectral-gated method is globally CG-consistent for every newest-retaining memory.
Use: the concrete gate implementation belongs to the same source information class as RFC.
Article: main_krylov, def:GRFC and def:classes, CG consistency on all positive quadratics.
Proof: the genuine quadratic history gives the scale-one true CG direction,
and the proved gated reference correction phase has only zero queries. -/
theorem gatedMethod_consistent (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k)
    (gamma : ℝ) : CGConsistent (gatedMethod memory gamma : ProbedMethod E) := by
  -- No local trajectory or desired response is assumed in this reference comparison.
  intro Q hQ hpos g k
  have hs := gatedMethod_static memory gamma Q hQ hpos g (fun k _ => hm k) k
  refine ⟨1,zero_lt_one,?_,?_⟩
  · change (retainedMethod memory _).direction _=1 • CG.direction Q g k
    rw [one_smul]
    exact retainedMethod_direction memory _ Q hQ hpos g k _ hs.1 hs.2 (fun _ => hm k)
  · exact gatedCorrection_reference memory gamma Q hQ hpos g k _ hs.1 hs.2 (fun _ => hm k)

end
end krylov.Correction
