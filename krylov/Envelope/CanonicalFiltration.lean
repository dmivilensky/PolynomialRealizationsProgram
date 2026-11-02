import krylov.Envelope.ActualFiltration
import krylov.Envelope.ExploredFlag

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and apB:lem:filtration, actual common transverse response.
Use: identify the genuine canonical explored flag with the true metric-root
Krylov image and derive the actual method-independent unexplored first
variation from the real frozen injection response, including exhaustion.
Source: genuine CG polynomial flags and actual normalized computed steps,
proved raw-method frozen filtration and real positive-root cancellation.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
variable {n : ℕ}

/-- The genuine finite explored canonical CG flag is exactly the real positive-root image of the actual polynomial Krylov space.
Use: The genuine finite explored canonical CG flag is exactly the real positive-root image of the actual polynomial Krylov space.
Article: main_krylov, thm:E and apB:lem:filtration, actual common transverse response.
Proof: Real positive CG lines identify canonical direction and step spans; true zero-safe normalization preserves both genuine span inclusions. -/
theorem exploredFlag_eq_primal_krylov (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (m : ℕ)
    (hpre : ∀ i<m, CG.gradient (cgOperator base) g i≠0) :
    exploredFlag base g m=(CG.krylovSpace (cgOperator base) g m).map
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)).toLinearMap := by
  -- Match the genuine direction, step and normalized-step spans through the actual positive metric root.
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  have hline (i : ℕ) (hi : i<m) : CG.length (cgOperator base) g i≠0 :=
    (CG.invariant_line_pos _ (cgOperator_positive base hb).2 g i
      (CG.invariant _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g i
        (fun j hj => hpre j (hj.trans hi))) (hpre i hi)).2.1.ne'
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hd := cgDirection_mem_krylov (cgOperator base) g i.val (fun j hj => hline j (by omega))
    have hd' := (krylovSpace_mono (cgOperator base) g (show i.val+1≤m by omega)) hd
    have hs : cgStep base g i.val∈CG.krylovSpace (cgOperator base) g m :=
      Submodule.smul_mem _ _ hd'
    have hR : canonicalCGStep base g i.val∈(CG.krylovSpace (cgOperator base) g m).map R.toLinearMap :=
      Submodule.mem_map_of_mem hs
    exact Submodule.smul_mem _ _ hR
  · apply Submodule.map_le_iff_le_comap.mpr
    rw [CG.krylovSpace_eq_span_directions _ g m hline]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change R (CG.direction (cgOperator base) g i)∈exploredFlag base g m
    have hs : canonicalCGStep base g i∈exploredFlag base g m := by
      have h := (exploredFlag base g m).smul_mem ‖canonicalCGStep base g i‖
        (Submodule.subset_span ⟨(⟨i,hi⟩ : Fin m),rfl⟩)
      change ‖canonicalCGStep base g i‖ • NormedSpace.normalize (canonicalCGStep base g i)∈exploredFlag base g m at h
      rw [NormedSpace.norm_smul_normalize] at h
      exact h
    rw [canonicalCG_direction base g i (canonicalCGStep_ne_zero base hb g i (fun j hj => hpre j (hj.trans_lt hi)))]
    exact Submodule.smul_mem _ _ hs

/-- The actual canonical inverse-root image of the genuine measured-CG frozen response driven by the true primitive segment derivatives.
Use: The actual canonical inverse-root image of the genuine measured-CG frozen response driven by the true primitive segment derivatives.
Article: main_krylov, thm:E and apB:lem:filtration, actual common transverse response.
Proof: Use the proved physical frozen executor and actual reference-step injections. -/
def canonicalFrozenResponse (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    (frozenResponse (cgOperator base) (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g)
      (referenceInjection (cgOperator base) g A) m 0)

/-- The genuine unexplored component of the actual canonical frozen injection response.
Use: The genuine unexplored component of the actual canonical frozen injection response.
Article: main_krylov, thm:E and apB:lem:filtration, actual common transverse response.
Proof: Remove the true orthogonal projection onto the actual finite explored CG flag. -/
def commonTransverseResponse (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  canonicalFrozenResponse base g A m-(exploredFlag base g m).starProjection (canonicalFrozenResponse base g A m)

/-- Every genuinely smooth source-admissible globally CG-consistent raw method has exactly the same true canonical unexplored first variation, given by the actual frozen reference injection response.
Use: Every genuinely smooth source-admissible globally CG-consistent raw method has exactly the same true canonical unexplored first variation, given by the actual frozen reference injection response.
Article: main_krylov, thm:E and apB:lem:filtration, actual common transverse response.
Proof: The proved actual physical gradient difference is the real reference operator image of a true Krylov displacement remainder. Genuine inverse-root cancellation places its actual canonical image in the explored flag; the real orthogonal projector therefore removes exactly that method-dependent difference. -/
theorem actual_common_transverse (memory : ℕ → ℕ) (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (hm : CGConsistent m) (hspan : ProbedSpanRestricted memory m)
    (A B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hA0 : A 0=fun _ => cgOperator base) (hB0 : B 0=fun _ => cgOperator base) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0)
    (hpre : ∀ i<N, CG.gradient (cgOperator base) g i≠0)
    (hsmooth : SmoothProbedCycleAt m 2 (cgOperator base) g N) :
    let D := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (deriv (fun t => probedGradient m (A t) (B t) g N) 0)
    D-(exploredFlag base g N).starProjection D=commonTransverseResponse base g A N := by
  let Rinv := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let D := Rinv (deriv (fun t => probedGradient m (A t) (B t) g N) 0)
  let F := canonicalFrozenResponse base g A N
  let P := exploredFlag base g N
  -- Use the proved complete raw-method filtration with genuine primitive oracle injections, including a true exhausted final gradient.
  have hfil := (actual_frozen_filtration memory m hm hspan A B g (cgOperator base)
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 hA0 hB0 N hA hB hpre hsmooth N le_rfl).2
  obtain ⟨v,hv,he⟩ := hfil
  -- The actual inverse-root reference-operator image is precisely a genuine root Krylov vector.
  have hDF : D-F∈P := by
    change Rinv _-Rinv _∈P
    rw [← map_sub,← he]
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (cgOperator base v)∈P
    rw [canonical_reference_action base hb]
    dsimp only [P]
    rw [exploredFlag_eq_primal_krylov base hb g N hpre]
    exact Submodule.mem_map_of_mem hv
  have hproj : P.starProjection (D-F)=D-F := P.starProjection_eq_self_iff.mpr hDF
  rw [map_sub] at hproj
  change D-P.starProjection D=F-P.starProjection F
  calc
    D-P.starProjection D=D-(P.starProjection D-P.starProjection F)-P.starProjection F := by abel
    _ = D-(D-F)-P.starProjection F := by rw [hproj]
    _ = F-P.starProjection F := by abel
end
end krylov.Envelope
