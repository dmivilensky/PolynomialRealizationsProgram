import krylov.Convergence.EvaluatedRankOneGeometry

/-!
Article: main_krylov, prop:EL, exact rank-one cubic coefficient.
Use: prove that the genuine evaluated-launch tensor response retains
precisely its first actual trial miss, with the printed sharp constant.
Source: true observed old flags, exact canonical midpoint geometry and
rank-one Riesz tensor algebra; no response identity is assumed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
  krylov.Tensor krylov.Correction krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The original evaluated-launch coefficient on the genuine first-axis
rank-one cubic is exactly M epsilon_0 c_0 h_0/2. Thus its first trial
error survives regardless of later trial choices. Article: prop:EL. -/
theorem evaluatedLaunchTensorCoefficient_rankOne
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) (M : ℝ)
    (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ a b c,(rankOneCubic (canonicalCGUnitStep base (cgOperator base u) 0) M).form
      (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c) :
    evaluatedLaunchTensorCoefficient trial base D u=
      (M/2*evaluatedTrialError trial base (cgOperator base u) 0*cgEnergy base (cgOperator base u) 0) •
        canonicalCGUnitStep base (cgOperator base u) 0 := by
  let g := cgOperator base u
  let S := cgOperator (metricRoot base)
  let e := canonicalCGUnitStep base g 0
  let T := rankOneCubic e M
  let P := fun l=>(oldFlag base g l).starProjection
  let ξ := fun l=>S (evaluatedLaunchReferenceMidpointDrift trial (cgOperator base) u l)
  let w := ∑ i∈range n,(evaluatedTrialError trial base g i*Real.sqrt (cgEnergy base g i)) •
    canonicalCGUnitStep base g i
  have hP l : cgOperator (transportedFlag (evaluatedCanonicalColumns trial base g) l)=P l :=
    evaluated_canonical_flags trial base hb g hc (fun i hi=>(ht i hi).ne') l
  have hPt l : cgOperator (transportedFlag (evaluatedCanonicalColumns trial base g) l)ᵀ=P l := by
    rw [cgOperator_transpose,hP]
    exact (Submodule.starProjection_isSymmetric _).clm_adjoint_eq
  have hslice l : cgOperator (metricRoot base)⁻¹*(D (evaluatedLaunchReferenceMidpointDrift trial (cgOperator base) u l))*
      cgOperator (metricRoot base)⁻¹=canonicalVariation T (ξ l) :=
    canonical_third_slice_eq base hb D T hT _
  have hPa l : P l e=e := (oldFlag base g l).starProjection_eq_self_iff.mpr
    (unitStep_mem_oldFlag base g (Nat.zero_le l))
  have hterm l : (P l*canonicalVariation T (ξ l)*P l) w=
      (M*inner ℝ e (ξ l)*inner ℝ e w) • e :=
    canonicalVariation_rankOneCubic_compression e M (P l) (Submodule.starProjection_isSymmetric _) (hPa l) (ξ l) w
  have hresponse : evaluatedLaunchTensorCoefficient trial base D u=
      (M*(∑ l∈range n,inner ℝ e (ξ l))*inner ℝ e w) • e := by
    change evaluatedLaunchResponse trial base g (fun l=>cgOperator (metricRoot base)⁻¹*
      (D (evaluatedLaunchReferenceMidpointDrift trial (cgOperator base) u l))*cgOperator (metricRoot base)⁻¹)=_
    unfold evaluatedLaunchResponse
    simp only [hP,hPt,hslice,_root_.sum_apply]
    change (∑ l∈range n,(P l*canonicalVariation T (ξ l)*P l) w)=_
    simp_rw [hterm]
    rw [←sum_smul]
    congr 1
    rw [mul_sum,sum_mul]
  rw [hresponse,evaluatedLaunch_midpoint_sum_first trial base hb u hc hn ht,
    evaluatedLaunch_accumulated_miss_first trial base hb g hc hn]
  congr 1
  have hsq : Real.sqrt (cgEnergy base g 0)^2=cgEnergy base g 0 :=
    Real.sq_sqrt ((cgEnergy_pos base hb g 0 (by rw [hc];exact hn)).le)
  change M*(Real.sqrt (cgEnergy base g 0)/2)*(evaluatedTrialError trial base g 0*Real.sqrt (cgEnergy base g 0))=
    M/2*evaluatedTrialError trial base g 0*cgEnergy base g 0
  calc
    _ = M/2*evaluatedTrialError trial base g 0*(Real.sqrt (cgEnergy base g 0))^2 := by ring
    _ = _ := by rw [hsq]

/-- Exact printed evaluated-launch norm on the genuine rank-one cubic.
Article: main_krylov, prop:EL. -/
theorem evaluatedLaunchTensorCoefficient_rankOne_norm
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) (M : ℝ) (hM : 0≤M)
    (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (evaluatedLaunchMethod trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ a b c,(rankOneCubic (canonicalCGUnitStep base (cgOperator base u) 0) M).form
      (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c) :
    ‖evaluatedLaunchTensorCoefficient trial base D u‖=
      M/2*|evaluatedTrialError trial base (cgOperator base u) 0| *cgEnergy base (cgOperator base u) 0 := by
  rw [evaluatedLaunchTensorCoefficient_rankOne trial base hb D u M hc hn ht hT,
    norm_smul,Real.norm_eq_abs,(canonicalCG_frame_of_full_atoms base hb (cgOperator base u) hc).norm_eq_one ⟨0,hn⟩,
    mul_one,abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤M/2),
    abs_of_nonneg (cgEnergy_pos base hb (cgOperator base u) 0 (by rw [hc];exact hn)).le]

end
end krylov.Convergence
