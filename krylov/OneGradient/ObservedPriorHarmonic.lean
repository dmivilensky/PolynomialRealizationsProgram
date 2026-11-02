import krylov.OneGradient.ObservedPriorFibre
import krylov.OneGradient.FibreExact
set_option autoImplicit false
/-!
Article: main_krylov, cor:quant, one harmonic endpoint rule on a known prior.
Use: evaluate one actual history-only prior policy on the genuine whole
physical information fibre, for spectral classes and arbitrary relative balls.
Source: complete observed/physical fibre dictionary, actual affine last-CG
curvature and exact scalar harmonic interval algebra.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual observed negative descent pairing for the full XRFC direction.
Use: prior endpoint trials retain the original physical line normalization.
Article: main_krylov, cor:quant. -/
def observedPriorSlope (H : History (EuclideanSpace ℝ (Fin (n+1)))) : ℝ :=
  -inner ℝ (virtualGradient H.pairs H.gradient) (xrfcPriorDirection H)

/-- All actual directional curvatures of the known prior consistent with the
real transcript, without selecting an unknown reference representative.
Use: the endpoint rule is one function of known data on the whole prior.
Article: main_krylov, cor:quant. -/
def observedPriorCurvatures (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ))
    (H : History (EuclideanSpace ℝ (Fin (n+1)))) : Set ℝ :=
  {c | ∃ C∈observedPriorMatrices prior H,
    (WithLp.ofLp (xrfcPriorDirection H)) ⬝ᵥ (C*ᵥ WithLp.ofLp (xrfcPriorDirection H))=c}

/-- One genuine prior-wide observed harmonic policy, defined from the actual
attained curvature endpoints and observed negative descent pairing.
Use: the unknown reference, its last pivot and unobserved output matrix are
absent from the decision function.
Article: main_krylov, cor:quant. -/
def observedPriorHarmonic (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ))
    (H : History (EuclideanSpace ℝ (Fin (n+1)))) : ℝ :=
  harmonicTrial (observedPriorSlope H/sSup (observedPriorCurvatures prior H))
    (observedPriorSlope H/sInf (observedPriorCurvatures prior H))

/-- The single transcript-based prior curvature set is precisely the actual
physical last-pivot interval in its genuine measured curvature units.
Use: both observed extrema are attained by real original prior matrices,
including zero interval width and a centre with different information.
Article: main_krylov, cor:quant.
Proof: actual observed actions identify exactly the whole positive physical
fibre. The true final CG descent pairing is the nonzero normal coefficient
squared, and every actual completion has its affine curvature. Positive
affine interval transport gives the exact range in both directions. -/
theorem observed_prior_curvature_range
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (H : History (EuclideanSpace ℝ (Fin (n+1))))
    (hy : ∀ j,windowImages H.pairs j=cgOperator A (windowSteps H.pairs j))
    (hspan : pairSpan H.pairs=CG.krylovSpace (cgOperator A) g n)
    (hgrad : virtualGradient H.pairs H.gradient=CG.gradient (cgOperator A) g n)
    (hdir : xrfcPriorDirection H=CG.direction (cgOperator A) g n)
    (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) (lo hi : ℝ)
    (hlo : lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹ < lo)
    (hprior : ∀ b : ℝ,lanczosCompletion A hA g hg hc b∈prior ↔ b∈Set.Icc lo hi) :
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    let q := observedPriorSlope H
    0 < q ∧ observedPriorCurvatures prior H=Set.Icc (q*(lo-sigma)) (q*(hi-sigma)) := by
  let Q := cgOperator A
  let r := CG.gradient Q g n
  let z := lastLanczosVector A hA g hg hc
  let gamma := inner ℝ z r
  let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  let q := observedPriorSlope H
  have hp := cgOperator_positive A hA
  have hpre (i : ℕ) (hi : i<n+1) : CG.gradient Q g i≠0 :=
    cg_nonstagnation A hA g i (by rw [full_gradient_atom_count A hA g hc];exact hi)
  have hinv := CG.invariant Q hp.1 hp.2 g n (fun i hi => hpre i (by omega))
  obtain ⟨hgeom,hgamma⟩ := last_cg_gradient_normal A hA g hg hc
  change r=gamma • z at hgeom
  change gamma≠0 at hgamma
  have hqgamma : q=gamma^2 := by
    change -inner ℝ (virtualGradient H.pairs H.gradient) (xrfcPriorDirection H)=gamma^2
    rw [hgrad,hdir,real_inner_comm,hinv.search_pair,neg_neg]
    change ‖r‖^2=gamma^2
    rw [hgeom,norm_smul,last_lanczos_unit A hA g hg hc,Real.norm_eq_abs,mul_one,sq_abs]
  have hq : 0 < q := hqgamma ▸ sq_pos_of_ne_zero hgamma
  have hcurv (b : ℝ) :
      (WithLp.ofLp (xrfcPriorDirection H)) ⬝ᵥ (lanczosCompletion A hA g hg hc b*ᵥ
        WithLp.ofLp (xrfcPriorDirection H))=q*(b-sigma) := by
    rw [← Matrix.inner_toEuclideanCLM]
    change inner ℝ (xrfcPriorDirection H) (cgOperator (lanczosCompletion A hA g hg hc b) (xrfcPriorDirection H))=_
    rw [hdir,completion_last_curvature,hqgamma]
    dsimp only [sigma,gamma,r,z,Q]
    ring
  refine ⟨hq,?_⟩
  ext c
  constructor
  · rintro ⟨C,hC,hcval⟩
    obtain ⟨b,_,rfl,hb⟩ := (observed_prior_matrices_fibre A hA g hg hc H hy hspan prior C).mp hC
    have hb' := (hprior b).mp hb
    rw [hcurv] at hcval
    rw [← hcval]
    exact ⟨mul_le_mul_of_nonneg_left (sub_le_sub_right hb'.1 sigma) hq.le,
      mul_le_mul_of_nonneg_left (sub_le_sub_right hb'.2 sigma) hq.le⟩
  · intro hcval
    let b := c/q+sigma
    have hb : b∈Set.Icc lo hi := by
      have hl : lo-sigma≤c/q := (le_div_iff₀ hq).mpr (by nlinarith [hcval.1])
      have hh : c/q≤hi-sigma := (div_le_iff₀ hq).mpr (by nlinarith [hcval.2])
      constructor <;> dsimp only [b] <;> linarith
    refine ⟨lanczosCompletion A hA g hg hc b,
      (observed_prior_matrices_fibre A hA g hg hc H hy hspan prior _).mpr
        ⟨b,hlo.trans_le hb.1,rfl,(hprior b).mpr hb⟩,?_⟩
    rw [hcurv]
    dsimp only [b]
    field_simp
    ring

/-- One observed prior-wide rule is exactly the harmonic trial of the true
physical fibre endpoints, with all observed extrema and positivity derived.
Use: no independently chosen fibre endpoints are captured by the policy;
this is the missing implementation dictionary in the uniform quantification.
Article: main_krylov, cor:quant.
Proof: the actual prior curvature range has positive ordered endpoints.
Its real infimum and supremum are those attained endpoints; the observed
positive descent pairing cancels their genuine common curvature scale. -/
theorem observed_prior_harmonic_dictionary
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (H : History (EuclideanSpace ℝ (Fin (n+1))))
    (hy : ∀ j,windowImages H.pairs j=cgOperator A (windowSteps H.pairs j))
    (hspan : pairSpan H.pairs=CG.krylovSpace (cgOperator A) g n)
    (hgrad : virtualGradient H.pairs H.gradient=CG.gradient (cgOperator A) g n)
    (hdir : xrfcPriorDirection H=CG.direction (cgOperator A) g n)
    (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) (lo hi : ℝ)
    (hlo : lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹ < lo)
    (horder : lo≤hi)
    (hprior : ∀ b : ℝ,lanczosCompletion A hA g hg hc b∈prior ↔ b∈Set.Icc lo hi) :
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    0 < observedPriorHarmonic prior H ∧ observedPriorHarmonic prior H=
      harmonicTrial (1/(hi-sigma)) (1/(lo-sigma)) := by
  let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
  let q := observedPriorSlope H
  obtain ⟨hq,hrange⟩ := observed_prior_curvature_range A hA g hg hc H hy hspan hgrad hdir prior lo hi hlo hprior
  have hq0 : q≠0 := hq.ne'
  have hordered : q*(lo-sigma)≤q*(hi-sigma) := mul_le_mul_of_nonneg_left (sub_le_sub_right horder sigma) hq.le
  have h1 : q/(q*(lo-sigma))=1/(lo-sigma) := by rw [div_mul_eq_div_div,div_self hq0]
  have h2 : q/(q*(hi-sigma))=1/(hi-sigma) := by rw [div_mul_eq_div_div,div_self hq0]
  have he : observedPriorHarmonic prior H=harmonicTrial (1/(hi-sigma)) (1/(lo-sigma)) := by
    rw [observedPriorHarmonic,hrange,csSup_Icc hordered,csInf_Icc hordered,h1,h2]
  have ha : 0 < 1/(hi-sigma) := one_div_pos.mpr (sub_pos.mpr (hlo.trans_le horder))
  have hab : 1/(hi-sigma)≤1/(lo-sigma) :=
    one_div_le_one_div_of_le (sub_pos.mpr hlo) (sub_le_sub_right horder sigma)
  exact ⟨he ▸ (harmonic_trial_attains ha hab).1,he⟩

/-- On the actual native XRFC last-query history the single known-prior
observed rule is precisely the true physical fibre harmonic trial.
Use: every action, span and virtual-geometry premise is derived from the
real executed method, rather than supplied to the final source theorem.
Article: main_krylov, cor:quant.
Proof: the native basis and CG reference theorem give the actual direction
and gradient. Genuine positive CG lengths identify its old polynomial flag;
the proved observed endpoint dictionary applies to that actual history. -/
theorem xrfc_observed_prior_harmonic
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (trial : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator A) g i)≠0)
    (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ)) (lo hi : ℝ)
    (hlo : lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹ < lo)
    (horder : lo≤hi)
    (hprior : ∀ b : ℝ,lanczosCompletion A hA g hg hc b∈prior ↔ b∈Set.Icc lo hi) :
    let H := oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator A) g n
    let sigma := lastJacobiPivot A hA g hg hc-(lastInversePivot A hA g hg hc)⁻¹
    0 < observedPriorHarmonic prior H ∧ observedPriorHarmonic prior H=
      harmonicTrial (1/(hi-sigma)) (1/(lo-sigma)) := by
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
  obtain ⟨_,hgrad,hdir⟩ := xrfc_full_reference trial Q hp.1 hp.2 g n
    (fun i hi => hpre i (by omega)) ht n le_rfl
  exact observed_prior_harmonic_dictionary A hA g hg hc H
    (fun j => oneGradientRun_pairs_quadratic method Q g n (H.pairs.get j) (List.get_mem _ j))
    hspan hgrad hdir prior lo hi hlo horder hprior

/-- One actual positive trial policy on the whole known prior, using arbitrary
positive earlier decisions and the same observed endpoint rule at the final query.
Use: no unknown reference or independently chosen information fibre is an input.
Article: main_krylov, cor:quant. -/
def observedPriorLastTrial (N : ℕ) (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ))
    (earlier : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ)
    (H : History (EuclideanSpace ℝ (Fin (n+1)))) : ℝ :=
  if H.records.length=N then
    if 0 < observedPriorHarmonic prior H then observedPriorHarmonic prior H else 1
  else earlier H

/-- Positive earlier decisions give a positive known-prior policy on every
history, with the true observed harmonic value on actual feasible source data.
Use: all real XRFC model domains are derived from the native execution.
Article: main_krylov, cor:quant.
Proof: the totalization is used only when the observed raw value is nonpositive. -/
theorem observed_prior_last_trial_positive (N : ℕ)
    (prior : Set (Matrix (Fin (n+1)) (Fin (n+1)) ℝ))
    (earlier : History (EuclideanSpace ℝ (Fin (n+1))) → ℝ) (he : ∀ H,0 < earlier H)
    (H : History (EuclideanSpace ℝ (Fin (n+1)))) : 0 < observedPriorLastTrial N prior earlier H := by
  unfold observedPriorLastTrial
  split_ifs with _ hh
  · exact hh
  · norm_num
  · exact he H

end
end krylov.OneGradient
