import krylov.Convergence.VirtualRankOneCoefficient

/-!
Article: main_krylov, thm:LB, actual last-axis cubic attainment.
Use: compute the true compatible XRFC tensor response on the genuine
last CG axis. Earlier slices vanish and the final oblique flag is the
identity, so both original bases have the same sharp scalar coefficient.
Source: actual terminal midpoint, genuine CG orthonormality and the true
full observed-column inverse; no attaining response is assumed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
  krylov.Tensor krylov.Correction krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual last old flag is the full identity, in the genuine
observed evaluated-step basis. Article: main_krylov, thm:LB. -/
theorem xrfc_last_projector_identity
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : E) (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) g i)≠0) :
    transportedFlag (xrfcCanonicalColumns trial base g) (n-1)=1 := by
  have hu := (xrfc_columns_nonsingular trial base hb g hc ht).2
  have hp : prefixProjection n (n-1)=1 := by
    have hf : (fun i : Fin n=>if i.val≤n-1 then (1:ℝ) else 0)=fun _=>1 := by
      funext i
      exact ite_eq_left (by have hi:=i.isLt;omega)
    rw [prefixProjection,hf,Matrix.diagonal_one]
  rw [transportedFlag,hp,Matrix.mul_one,Matrix.mul_nonsing_inv _ hu]

/-- The actual terminal compatible midpoint has the exact half last-step
coordinate on the true final CG axis. Article: main_krylov, thm:LB. -/
theorem xrfc_midpoint_last_last
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)) :
    inner ℝ (canonicalCGUnitStep base (cgOperator base u) (n-1))
      (cgOperator (metricRoot base) (xrfcReferenceMidpointDrift trial (cgOperator base) u (n-1)))=
      Real.sqrt (cgEnergy base (cgOperator base u) (n-1))/2 := by
  let g := cgOperator base u
  let S := cgOperator (metricRoot base)
  let e := canonicalCGUnitStep base g (n-1)
  have hlast : inner ℝ e (S (referenceStep (cgOperator base) g (n-1)))=Real.sqrt (cgEnergy base g (n-1)) := by
    have hh := canonical_step_unit_pair base hb g ⟨n-1,by rw [hc];omega⟩ ⟨n-1,by rw [hc];omega⟩
    simpa only [e,S,referenceStep,canonicalCGStep,cgStep,cgLine,cgOperator,ite_true,cgEnergy_sqrt base hb] using hh
  have hprev : inner ℝ e (S (xrfcPreviousMiss trial (cgOperator base) g (n-1)))=0 := by
    unfold xrfcPreviousMiss
    split_ifs with hz
    · rw [map_zero,inner_zero_right]
    · have hidx : n-1-1<n := by omega
      rw [xrfcReferenceMiss_canonical trial base hb g (n-1-1) (by rw [hc];exact hidx),inner_smul_right]
      have hh := canonical_step_unit_pair base hb g ⟨n-1,by rw [hc];omega⟩ ⟨n-1-1,by rw [hc];exact hidx⟩
      have he : (⟨n-1,by rw [hc];omega⟩ : Fin (referenceAtomCount base hb g))≠⟨n-1-1,by rw [hc];exact hidx⟩ := by
        intro he
        have hi := congrArg Fin.val he
        change n-1=n-1-1 at hi
        omega
      rw [ite_eq_right he] at hh
      rw [show inner ℝ e (canonicalCGStep base g (n-1-1))=0 from hh,mul_zero]
  rw [xrfcReferenceMidpointDrift_terminal trial base hb u hc hn ht,map_smul,map_add,inner_smul_right,inner_add_right]
  change (1/2:ℝ)*(inner ℝ e (S (xrfcPreviousMiss trial (cgOperator base) g (n-1)))+
    inner ℝ e (S (referenceStep (cgOperator base) g (n-1))))=_
  rw [hprev,hlast]
  ring

/-- Literal compatible last-axis cubic response of the actual step-basis
XRFC execution. Its final amplitude has no earlier-trial multiplier.
Article: main_krylov, thm:LB, sharp rank-one attainment. -/
theorem xrfcTensorCoefficient_last_rankOne
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) (M : ℝ)
    (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ a b c,(rankOneCubic (canonicalCGUnitStep base (cgOperator base u) (n-1)) M).form
      (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c) :
    xrfcTensorCoefficient trial base D u=
      (xrfcTrialCoefficient trial base (cgOperator base u) n (n-1)*M*
        Real.sqrt (cgEnergy base (cgOperator base u) (n-1))/2) • canonicalCGUnitStep base (cgOperator base u) (n-1) := by
  let g := cgOperator base u
  let e := canonicalCGUnitStep base g (n-1)
  let T := rankOneCubic e M
  let ξ := fun l=>cgOperator (metricRoot base) (xrfcReferenceMidpointDrift trial (cgOperator base) u l)
  have ho := canonicalCG_frame_of_full_atoms base hb g hc
  have hpair (l : ℕ) (hl : l<n) : inner ℝ e (canonicalCGUnitStep base g l)=if l=n-1 then 1 else 0 := by
    have hh := orthonormal_iff_ite.mp ho ⟨n-1,by omega⟩ ⟨l,hl⟩
    simpa only [Fin.mk.injEq,eq_comm] using hh
  have hslice l : cgOperator (metricRoot base)⁻¹*(D (xrfcReferenceMidpointDrift trial (cgOperator base) u l))*
      cgOperator (metricRoot base)⁻¹=canonicalVariation T (ξ l) :=
    canonical_third_slice_eq base hb D T hT _
  change xrfcStepResponse trial base g _=_
  unfold xrfcStepResponse
  simp only [hslice]
  rw [sum_eq_single (n-1)]
  · rw [canonicalVariation_rankOneCubic_apply,hpair (n-1) (by omega),ite_eq_left rfl,mul_one,
      xrfc_midpoint_last_last trial base hb u hc hn ht,
      xrfc_last_projector_identity trial base hb g hc hn (fun i hi=>(ht i hi).ne'),Matrix.transpose_one]
    simp only [cgOperator,map_one,one_apply_eq_self,smul_smul]
    congr 1
    dsimp only [g,cgOperator]
    ring
  · intro b hb hne
    rw [canonicalVariation_rankOneCubic_apply,hpair b (mem_range.mp hb),ite_eq_right hne,
      mul_zero,zero_smul,map_zero,smul_zero]
  · intro hnot
    exact (hnot (mem_range.mpr (by omega))).elim

/-- Exact source attainment: the real last-axis tensor coefficient has
norm M|epsilon_last|c_last/2, in the actual step basis without any oblique
amplification. Article: main_krylov, thm:LB. -/
theorem xrfcTensorCoefficient_last_rankOne_norm
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) (M : ℝ) (hM : 0≤M)
    (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ a b c,(rankOneCubic (canonicalCGUnitStep base (cgOperator base u) (n-1)) M).form
      (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c) :
    ‖xrfcTensorCoefficient trial base D u‖=
      M/2*|1-trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) (n-1))/
        CG.length (cgOperator base) (cgOperator base u) (n-1)| *cgEnergy base (cgOperator base u) (n-1) := by
  rw [xrfcTensorCoefficient_last_rankOne trial base hb D u M hc hn ht hT,norm_smul,Real.norm_eq_abs,
    (canonicalCG_frame_of_full_atoms base hb (cgOperator base u) hc).norm_eq_one ⟨n-1,by omega⟩,
    mul_one,abs_div,abs_mul,abs_mul,abs_of_nonneg hM,abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (by norm_num : (0:ℝ)≤2),
    xrfc_trial_coefficient_abs trial base hb (cgOperator base u) n (n-1) (by rw [hc];omega)]
  simp only [show n-1+1=n by omega,Ico_self]
  have hs : Real.sqrt (cgEnergy base (cgOperator base u) (n-1))^2=cgEnergy base (cgOperator base u) (n-1) :=
    Real.sq_sqrt ((cgEnergy_pos base hb (cgOperator base u) (n-1) (by rw [hc];omega)).le)
  calc
    _ = M/2*|1-trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) (n-1))/
        CG.length (cgOperator base) (cgOperator base u) (n-1)| *
        Real.sqrt (cgEnergy base (cgOperator base u) (n-1))^2 := by ring
    _ = _ := by rw [hs]

end
end krylov.Convergence
