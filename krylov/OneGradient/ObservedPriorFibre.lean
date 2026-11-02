import krylov.OneGradient.XRFCObservedSpectral
import krylov.OneGradient.CompletionCG
set_option autoImplicit false
/-!
Article: main_krylov, cor:quant, one observed rule on the whole known prior.
Use: identify actual transcript-consistent prior matrices with the entire
original physical information fibre, before selecting endpoint trials.
Source: native XRFC full observed basis, genuine polynomial Krylov flags and
the proved complete positive physical information-fibre theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods
variable {n : ℕ}

/-- All positive matrices in the known prior consistent with the genuine
observed step/image pairs, defined entirely from those known data.
Use: one prior-dependent rule can be used on every original information fibre.
Article: main_krylov, cor:quant. -/
def observedPriorMatrices (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ))
    (H : History (EuclideanSpace ℝ (Fin (n+1)))) : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :=
  {C | C.PosDef ∧ C∈prior ∧ ∀ j, cgOperator C (windowSteps H.pairs j)=windowImages H.pairs j}

/-- Once the genuine measured steps span the actual old Krylov space, the
single observed prior class is exactly the original whole physical fibre
intersected with that prior, including its strict positivity domain.
Use: spectral and relative-ball policies read one common actual transcript
rule rather than capture separately chosen fibre endpoints.
Article: main_krylov, cor:quant and s5:fibre(a).
Proof: equality of the real measured actions extends linearly to their
proved full old Krylov span. The already proved complete physical fibre
then identifies precisely the positive last-diagonal completions. -/
theorem observed_prior_matrices_fibre
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (H : History (EuclideanSpace ℝ (Fin (n+1))))
    (hy : ∀ j,windowImages H.pairs j=cgOperator A (windowSteps H.pairs j))
    (hspan : pairSpan H.pairs=CG.krylovSpace (cgOperator A) g n)
    (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) (C : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    C∈observedPriorMatrices prior H ↔ ∃ b : ℝ,
      lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹ < b ∧
        C=lanczosCompletion A hA g hg hc b ∧ C∈prior := by
  constructor
  · rintro ⟨hC,hprior,hdata⟩
    let D := cgOperator C-cgOperator A
    have hker : pairSpan H.pairs≤D.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      change cgOperator C (windowSteps H.pairs j)-cgOperator A (windowSteps H.pairs j)=0
      exact sub_eq_zero.mpr ((hdata j).trans (hy j))
    have hact : ∀ v∈CG.krylovSpace (cgOperator A) g n,cgOperator C v=cgOperator A v := by
      intro v hv
      rw [← hspan] at hv
      exact sub_eq_zero.mp (hker hv)
    obtain ⟨b,hb,he⟩ := (physical_information_fibre A hA g hg hc C).mp ⟨hC,hact⟩
    exact ⟨b,hb,he,hprior⟩
  · rintro ⟨b,hb,rfl,hprior⟩
    refine ⟨(lanczos_completion_positive_iff A hA g hg hc b).mpr hb,hprior,?_⟩
    intro j
    have hv : windowSteps H.pairs j∈CG.krylovSpace (cgOperator A) g n := by
      rw [← hspan]
      exact Submodule.subset_span ⟨j,rfl⟩
    exact (lanczos_completion_information A hA g hg hc b _ hv).trans (hy j).symm

/-- On every actual full-memory XRFC last-query history, the one observed
prior class is exactly the original entire physical information fibre.
Use: the dictionary derives its old-space and action premises by running the
real method, for any nonzero earlier observed trial choices.
Article: main_krylov, cor:quant.
Proof: native XRFC gives the true measured basis and actions. Genuine CG
positive lines identify its direction flag with the original polynomial
Krylov space; the general observed/physical fibre dictionary then applies. -/
theorem xrfc_observed_prior_fibre
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator A) g i)≠0)
    (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) (C : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    let H := oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator A) g n
    C∈observedPriorMatrices prior H ↔ ∃ b : ℝ,
      lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹ < b ∧
        C=lanczosCompletion A hA g hg hc b ∧ C∈prior := by
  let Q := cgOperator A
  let method := xrfcMethod fullMemory trial
  let H := oneGradientRun method (fun _ => Q) g n
  have hp := cgOperator_positive A hA
  have hpre (i : ℕ) (hi : i<n+1) : CG.gradient Q g i≠0 :=
    cg_nonstagnation A hA g i (by rw [full_gradient_atom_count A hA g hc];exact hi)
  have hb := xrfc_full_basis trial Q hp.1 hp.2 g n (fun i hi => hpre i (by omega)) ht n le_rfl
  have hline (i : ℕ) (hi : i<n) : CG.length Q g i≠0 :=
    (CG.invariant_line_pos Q hp.2 g i (CG.invariant Q hp.1 hp.2 g i
      (fun j hj => hpre j (by omega))) (hpre i (by omega))).2.1.ne'
  have hspan : pairSpan H.pairs=CG.krylovSpace Q g n :=
    hb.2.trans (CG.krylovSpace_eq_span_directions Q g n hline).symm
  exact observed_prior_matrices_fibre A hA g hg hc H
    (fun j => oneGradientRun_pairs_quadratic method Q g n (H.pairs.get j) (List.get_mem _ j)) hspan prior C

end
end krylov.OneGradient
