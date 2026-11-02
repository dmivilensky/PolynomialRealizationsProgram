import krylov.Convergence.OneGradientRankOne
import krylov.Convergence.OneGradientTrialMiss
import krylov.Tensor.ReferenceLowerBound

/-!
Article: main_krylov, prop:EL, exact oldest-coordinate geometry.
Use: identify the rank-one cubic on the genuine first CG axis. The
coordinates are derived from actual evaluated-launch segments, not
supplied midpoint or trial-error identities.
Source: true CG orthogonality, actual reference midpoint telescoping and
positive exact-search normalization.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
  krylov.Tensor krylov.Correction krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual oldest unit CG direction extracts minus its own step
length from the genuine starting error. Article: prop:EL. -/
theorem canonical_first_initial_coordinate
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (u : E)
    (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n) :
    inner ℝ (canonicalCGUnitStep base (cgOperator base u) 0) (cgOperator (metricRoot base) u)=
      -Real.sqrt (cgEnergy base (cgOperator base u) 0) := by
  let g := cgOperator base u
  have hs : canonicalCGStep base g 0≠0 := canonicalCGStep_ne_zero base hb g 0 (fun i hi=>cg_nonstagnation base hb g i (by rw [hc];omega))
  have hpost := canonicalCG_postsearch_orth base hb g 0 hs
  change inner ℝ (canonicalCGUnitStep base g 0) (cgCanonicalError base g (0+1))=0 at hpost
  rw [cgCanonicalError_succ base hb,inner_add_right] at hpost
  have hpair := canonical_step_unit_pair base hb g ⟨0,by rw [hc];exact hn⟩ ⟨0,by rw [hc];exact hn⟩
  simp only [ite_true] at hpair
  have hi : cgCanonicalError base g 0=cgOperator (metricRoot base) u := by
    change Matrix.toEuclideanCLM (𝕜:=ℝ) (metricRoot base)⁻¹ (cgOperator base u)=_
    exact canonical_reference_action base hb u
  rw [hi,hpair,←cgEnergy_sqrt base hb] at hpost
  linarith only [hpost]

/-- The actual evaluated-launch missed segment has exactly its genuine
relative trial-error coordinate on every active CG axis.
Article: main_krylov, prop:EL. -/
theorem evaluatedLaunchReferenceMiss_canonical
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (i : ℕ) (hi : i<referenceAtomCount base hb g) :
    cgOperator (metricRoot base) (evaluatedLaunchReferenceMiss trial (cgOperator base) g i)=
      evaluatedTrialError trial base g i • canonicalCGStep base g i :=
  canonical_relative_trial_miss base hb g i hi _

/-- Actual first-axis coordinates extract precisely the first trial
miss from the full accumulated evaluated-launch error.
Article: main_krylov, prop:EL. -/
theorem evaluatedLaunch_accumulated_miss_first
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (hc : referenceAtomCount base hb g=n) (hn : 0<n) :
    inner ℝ (canonicalCGUnitStep base g 0)
      (∑ i∈range n,(evaluatedTrialError trial base g i*Real.sqrt (cgEnergy base g i)) •
        canonicalCGUnitStep base g i)=evaluatedTrialError trial base g 0*Real.sqrt (cgEnergy base g 0) := by
  have ho := canonicalCG_frame_of_full_atoms base hb g hc
  have hpair (i : ℕ) (hi : i<n) : inner ℝ (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g i)=
      if i=0 then 1 else 0 := by
    have hh := orthonormal_iff_ite.mp ho ⟨0,hn⟩ ⟨i,hi⟩
    simpa only [Fin.mk.injEq,eq_comm] using hh
  rw [inner_sum]
  have he : (∑ i∈range n,inner ℝ (canonicalCGUnitStep base g 0)
      ((evaluatedTrialError trial base g i*Real.sqrt (cgEnergy base g i)) • canonicalCGUnitStep base g i))=
      ∑ i∈range n,if i=0 then evaluatedTrialError trial base g 0*Real.sqrt (cgEnergy base g 0) else 0 := by
    apply sum_congr rfl
    intro i hi
    rw [inner_smul_right,hpair i (mem_range.mp hi)]
    split_ifs with hz
    · subst i;rw [mul_one]
    · rw [mul_zero]
  rw [he,sum_ite_eq']
  rw [ite_eq_left (mem_range.mpr hn)]

/-- The full sum of true canonical evaluated midpoint differences has
exactly half the first genuine CG step on its oldest coordinate.
Article: main_krylov, prop:EL, rank-one cubic identity. -/
theorem evaluatedLaunch_midpoint_sum_first
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _=>cgOperator base) (cgOperator base u) i)) :
    (∑ l∈range n,inner ℝ (canonicalCGUnitStep base (cgOperator base u) 0)
      (cgOperator (metricRoot base) (evaluatedLaunchReferenceMidpointDrift trial (cgOperator base) u l)))=
      Real.sqrt (cgEnergy base (cgOperator base u) 0)/2 := by
  let m := evaluatedLaunchMethod trial
  let Q := cgOperator base
  let g := Q u
  let S := cgOperator (metricRoot base)
  let e := canonicalCGUnitStep base g 0
  let p := oneGradientReferencePoint m Q u
  let mid := oneGradientReferenceMidpoint m Q u n
  have hsum : (∑ l∈range n,inner ℝ e (S (evaluatedLaunchReferenceMidpointDrift trial Q u l)))=
      inner ℝ e (S (mid n-mid 0)) := by
    simp only [evaluatedLaunchReferenceMidpointDrift,map_sub,inner_sub_right]
    exact sum_range_sub (fun l=>inner ℝ e (S (mid l))) n
  rw [hsum]
  have hout := evaluatedLaunchReferenceOutput_zero trial base hb u hc ht
  change oneGradientReferenceOutput m Q u n=0 at hout
  have hmidn : mid n=(1/2:ℝ) • p n := by
    simp only [mid,oneGradientReferenceMidpoint,ite_eq_right (lt_irrefl n),hout,add_zero]
    rfl
  have hmid0 : mid 0=(1/2:ℝ) • (p 0+p 1) := by
    simp only [mid,oneGradientReferenceMidpoint,ite_eq_left hn]
    rfl
  have hp0 : p 0=u := by
    simp only [p,oneGradientReferencePoint,oneGradientRun,History.displacement,List.map_nil,List.sum_nil,add_zero]
  have hgrad := oneGradientRun_quadratic_gradient m Q g n
  have hpgrad : S (p n)=cgOperator (metricRoot base)⁻¹ (oneGradientRun m (fun _=>Q) g n).gradient := by
    rw [hgrad]
    change S (u+(oneGradientRun m (fun _=>Q) g n).displacement)=_
    rw [show g+Q (oneGradientRun m (fun _=>Q) g n).displacement=
      Q (u+(oneGradientRun m (fun _=>Q) g n).displacement) by rw [map_add]]
    exact (canonical_reference_action base hb _).symm
  have hpn : inner ℝ e (S (p n))= -evaluatedTrialError trial base g 0*Real.sqrt (cgEnergy base g 0) := by
    rw [hpgrad,evaluated_canonical_error trial base hb g hc (fun i hi=>(ht i hi).ne'),inner_neg_right,
      evaluatedLaunch_accumulated_miss_first trial base hb g hc hn]
    ring
  have hstep := evaluatedLaunchReferencePoint_step trial base hb u hc (fun i hi=>(ht i hi).ne') 0 hn
  have hp1 : inner ℝ e (S (p 1))= -evaluatedTrialError trial base g 0*Real.sqrt (cgEnergy base g 0) := by
    have heq : p 1=p 0+referenceStep Q g 0-evaluatedLaunchReferenceMiss trial Q g 0 := by
      change p 1-p 0=referenceStep Q g 0-evaluatedLaunchReferenceMiss trial Q g 0 at hstep
      calc
        p 1 = p 0+(p 1-p 0) := by module
        _ = _ := by rw [hstep];module
    rw [heq,map_sub,map_add,inner_sub_right,inner_add_right,hp0,canonical_first_initial_coordinate base hb u hc hn,
      evaluatedLaunchReferenceMiss_canonical trial base hb g 0 (by rw [hc];exact hn)]
    have hpair := canonical_step_unit_pair base hb g ⟨0,by rw [hc];exact hn⟩ ⟨0,by rw [hc];exact hn⟩
    simp only [ite_true] at hpair
    change -Real.sqrt (cgEnergy base g 0)+inner ℝ e (canonicalCGStep base g 0)-
      inner ℝ e (evaluatedTrialError trial base g 0 • canonicalCGStep base g 0)=_
    rw [inner_smul_right,hpair,←cgEnergy_sqrt base hb]
    ring
  rw [hmidn,hmid0,map_sub,map_smul,map_smul,map_add,inner_sub_right,inner_smul_right,
    inner_smul_right,inner_add_right,hpn,hp0,canonical_first_initial_coordinate base hb u hc hn,hp1]
  ring

end
end krylov.Convergence
