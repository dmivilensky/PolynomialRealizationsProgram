import krylov.OneGradient.EvaluatedCanonical
import krylov.LinearAlgebra.EvaluatedSupport
set_option autoImplicit false
/-!
Article: main_krylov, prop:launch(a), actual sharp evaluated-launch comparisons.
Use: prove the printed support maximum and both original trial-error bounds
for the real native evaluated-launch execution and its true canonical flags.
Source: genuine canonical evaluated error, actual orthonormal CG frame and
the proved attained independent symmetric budget support.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace NNReal
variable {n : ℕ}

/-- The actual evaluated canonical launch has exactly the source squared
energy sum of every genuine measured relative trial error.
Use: the upper comparison uses the real launch norm, including all old misses.
Article: main_krylov, prop:launch(a).
Proof: the actual complete canonical error sum lies in the proved genuine
orthonormal CG unit-step frame; each square-root energy squares to its true energy. -/
theorem evaluated_error_norm_sq (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g i)≠0) :
    let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g n
    ‖cgOperator (metricRoot base)⁻¹ H.gradient‖^2=
      ∑ i∈Finset.range n,(evaluatedTrialError trial base g i)^2*cgEnergy base g i := by
  have ho := canonicalCGUnitStep_orthonormal base hb g n
    (fun i hi => cg_nonstagnation base hb g i (by omega))
  dsimp only
  rw [evaluated_canonical_error trial base hb g hc ht,norm_neg,← real_inner_self_eq_norm_sq,
    ← Fin.sum_univ_eq_sum_range,ho.inner_sum]
  change (∑ i : Fin n,(evaluatedTrialError trial base g i.val*Real.sqrt (cgEnergy base g i.val))*
    (evaluatedTrialError trial base g i.val*Real.sqrt (cgEnergy base g i.val)))=_
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (evaluatedTrialError trial base g i*Real.sqrt (cgEnergy base g i))*
    (evaluatedTrialError trial base g i*Real.sqrt (cgEnergy base g i))) n]
  apply Finset.sum_congr rfl
  intro i hi
  have he := (cgEnergy_pos base hb g i (by have := Finset.mem_range.mp hi;omega)).le
  rw [← pow_two,mul_pow,Real.sq_sqrt he]

/-- The first actual unit CG component of the evaluated canonical launch
is its original negative first relative miss times the true root energy.
Use: yields the source lower comparison from a real preserved direction.
Article: main_krylov, prop:launch(a).
Proof: actual canonical evaluated error and genuine CG orthonormality remove
every later component exactly. -/
theorem evaluated_error_first_component (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (ht : ∀ i<n,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g i)≠0) :
    let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g n
    inner ℝ (canonicalCGUnitStep base g 0) (cgOperator (metricRoot base)⁻¹ H.gradient)=
      -(evaluatedTrialError trial base g 0*Real.sqrt (cgEnergy base g 0)) := by
  have ho := canonicalCGUnitStep_orthonormal base hb g n
    (fun i hi => cg_nonstagnation base hb g i (by omega))
  dsimp only
  rw [evaluated_canonical_error trial base hb g hc ht,inner_neg_right,← Fin.sum_univ_eq_sum_range,inner_sum]
  congr 1
  let first : Fin n := ⟨0,hn⟩
  change (∑ i : Fin n,inner ℝ (canonicalCGUnitStep base g first.val)
    ((evaluatedTrialError trial base g i.val*Real.sqrt (cgEnergy base g i.val)) •
      canonicalCGUnitStep base g i.val))=_
  have he (i : Fin n) : inner ℝ (canonicalCGUnitStep base g first.val)
      (canonicalCGUnitStep base g i.val)=(if first=i then 1 else 0) :=
    orthonormal_iff_ite.mp ho first i
  simp_rw [real_inner_smul_right,he]
  simp [first]

/-- The genuine evaluated-launch compression response has the exact
attained support maximum and both source trial-error comparison bounds.
Use: every projector and the canonical launch come from actual recorded
steps of the implemented evaluated procedure, not from prescribed CG columns.
Article: main_krylov, prop:launch(a).
Proof: actual native canonical flags are the real orthogonal CG prefixes.
Apply attained symmetric box duality, their true contraction bounds and the
common preserved first actual unit CG direction; insert the proved real launch
component and norm identities. -/
theorem evaluated_launch_sharp_comparison
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (ht : ∀ i<n+1,trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g i)≠0)
    (omega : ℕ → ℝ≥0) :
    let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g (n+1)
    let e := cgOperator (metricRoot base)⁻¹ H.gradient
    let P := fun l => cgOperator (transportedFlag (evaluatedCanonicalColumns trial base g) l)
    ∃ C : ℝ≥0,
      IsGreatest ((fun u : EuclideanSpace ℝ (Fin (n+1)) =>
        ∑ i∈Finset.range (n+1),(omega i : ℝ)*‖P i u‖*‖P i e‖) '' {u | ‖u‖=1}) (C : ℝ) ∧
      IsGreatest {z : ℝ | ∃ T : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)),
        (∀ i<n+1,IsSelfAdjoint (T i) ∧ ‖T i‖≤(omega i : ℝ)) ∧
        z=‖evaluatedLaunchResponse (Finset.range (n+1)) P e T‖} (C : ℝ) ∧
      (∑ i∈Finset.range (n+1),(omega i : ℝ))*|evaluatedTrialError trial base g 0| *
        Real.sqrt (cgEnergy base g 0)≤(C : ℝ) ∧
      (C : ℝ)≤(∑ i∈Finset.range (n+1),(omega i : ℝ))*
        Real.sqrt (∑ i∈Finset.range (n+1),(evaluatedTrialError trial base g i)^2*cgEnergy base g i) := by
  let H := oneGradientRun (evaluatedLaunchMethod trial) (fun _ => cgOperator base) g (n+1)
  let e := cgOperator (metricRoot base)⁻¹ H.gradient
  let P := fun l => cgOperator (transportedFlag (evaluatedCanonicalColumns trial base g) l)
  obtain ⟨C,hC,hout⟩ := evaluated_launch_response_sharp (Finset.range (n+1)) omega P e
  have hP (l : ℕ) : P l=(oldFlag base g l).starProjection :=
    evaluated_canonical_flags trial base hb g hc ht l
  refine ⟨C,hC,?_,?_,?_⟩
  · simpa only [Finset.mem_range] using hout
  · have hfirst := firstStep_common base hb g (by omega)
    have hl := evaluated_launch_support_lower (Finset.range (n+1)) omega P e (C : ℝ) hC
      (canonicalCGUnitStep base g 0) hfirst.1
      (fun l _ => by rw [hP];exact (Submodule.starProjection_isSymmetric _).clm_adjoint_eq)
      (fun l _ => by rw [hP];exact Submodule.starProjection_eq_self_iff.mpr (hfirst.2 l))
    rw [evaluated_error_first_component trial base hb g hc (by omega) ht,abs_neg,abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)] at hl
    simpa only [mul_assoc] using hl
  · have hu := evaluated_launch_support_upper (Finset.range (n+1)) omega P e (C : ℝ) hC
      (fun l _ v => by rw [hP];exact Submodule.norm_starProjection_apply_le _ v)
    have hn := evaluated_error_norm_sq trial base hb g hc ht
    have heq : Real.sqrt (∑ i∈Finset.range (n+1),(evaluatedTrialError trial base g i)^2*
        cgEnergy base g i)=‖e‖ := by
      rw [← hn,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
    rw [heq]
    exact hu

end
end krylov.OneGradient
