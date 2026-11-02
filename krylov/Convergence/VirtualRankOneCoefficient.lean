import krylov.Convergence.VirtualRankOneGeometry

/-!
Article: main_krylov, prop:EL, exact virtual rank-one forgetting.
Use: compute the actual oldest-axis tensor coefficient and its printed
product of later relative virtual corrections, including the genuine
oblique projector amplification in the evaluated-step basis.
Source: true rank-one tensor slices, actual CG frame orthogonality and
the exact measured XRFC amplitudes.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
  krylov.Tensor krylov.Correction krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The actual virtual-launch rank-one cubic response has only its
first source slice, with the exact original first amplitude.
Article: main_krylov, prop:EL. -/
theorem xrfcTensorCoefficient_rankOne
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) (M : ℝ)
    (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ a b c,(rankOneCubic (canonicalCGUnitStep base (cgOperator base u) 0) M).form
      (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c) :
    xrfcTensorCoefficient trial base D u=
      (xrfcTrialCoefficient trial base (cgOperator base u) n 0*M*
        Real.sqrt (cgEnergy base (cgOperator base u) 0)/2) •
        cgOperator (transportedFlag (xrfcCanonicalColumns trial base (cgOperator base u)) 0)ᵀ
          (canonicalCGUnitStep base (cgOperator base u) 0) := by
  let g := cgOperator base u
  let e := canonicalCGUnitStep base g 0
  let T := rankOneCubic e M
  let ξ := fun l=>cgOperator (metricRoot base) (xrfcReferenceMidpointDrift trial (cgOperator base) u l)
  have ho := canonicalCG_frame_of_full_atoms base hb g hc
  have hpair (l : ℕ) (hl : l<n) : inner ℝ e (canonicalCGUnitStep base g l)=if l=0 then 1 else 0 := by
    have hh := orthonormal_iff_ite.mp ho ⟨0,hn⟩ ⟨l,hl⟩
    simpa only [Fin.mk.injEq,eq_comm] using hh
  have hslice l : cgOperator (metricRoot base)⁻¹*(D (xrfcReferenceMidpointDrift trial (cgOperator base) u l))*
      cgOperator (metricRoot base)⁻¹=canonicalVariation T (ξ l) :=
    canonical_third_slice_eq base hb D T hT _
  change xrfcStepResponse trial base g _=_
  unfold xrfcStepResponse
  simp only [hslice]
  rw [sum_eq_single 0]
  · rw [canonicalVariation_rankOneCubic_apply,hpair 0 hn,ite_eq_left rfl,mul_one,
      xrfc_midpoint_first_first trial base hb u hc hn ht,map_smul,smul_smul]
    congr 1
    ring
  · intro b hb hne
    rw [canonicalVariation_rankOneCubic_apply,hpair b (mem_range.mp hb),ite_eq_right hne,
      mul_zero,zero_smul,map_zero,smul_zero]
  · intro hnot
    exact (hnot (mem_range.mpr hn)).elim

/-- Exact original virtual forgetting product, with the real evaluated
step-basis oblique factor retained. Article: main_krylov, prop:EL. -/
theorem xrfcTensorCoefficient_rankOne_norm
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) (M : ℝ) (hM : 0≤M)
    (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ a b c,(rankOneCubic (canonicalCGUnitStep base (cgOperator base u) 0) M).form
      (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c) :
    let g := cgOperator base u
    let τ := fun i=>trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) g i)
    ‖xrfcTensorCoefficient trial base D u‖=
      M/2*|1-τ 0/CG.length (cgOperator base) g 0| *
        (∏ i∈Ico 1 n,|(CG.length (cgOperator base) g i-τ i)/τ i|)*
        cgEnergy base g 0*‖cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) 0)‖ := by
  dsimp only
  rw [xrfcTensorCoefficient_rankOne trial base hb D u M hc hn ht hT,norm_smul,Real.norm_eq_abs,
    abs_div,abs_mul,abs_mul,abs_of_nonneg hM,abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (by norm_num : (0:ℝ)≤2),
    xrfc_first_projector_transpose_norm trial base hb (cgOperator base u) hc hn (fun i hi=>(ht i hi).ne'),
    xrfc_trial_coefficient_abs trial base hb (cgOperator base u) n 0 (by rw [hc];exact hn)]
  have hsq : Real.sqrt (cgEnergy base (cgOperator base u) 0)^2=cgEnergy base (cgOperator base u) 0 :=
    Real.sq_sqrt ((cgEnergy_pos base hb (cgOperator base u) 0 (by rw [hc];exact hn)).le)
  calc
    _ = M/2*|1-trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) 0)/
        CG.length (cgOperator base) (cgOperator base u) 0| *
      (∏ i∈Ico 1 n,|(CG.length (cgOperator base) (cgOperator base u) i-
        trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))/
        trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)|)*
      (Real.sqrt (cgEnergy base (cgOperator base u) 0))^2*
      ‖cgOperator (transportedFlag (xrfcCanonicalColumns trial base (cgOperator base u)) 0)‖ := by ring
    _ = _ := by rw [hsq]

end
end krylov.Convergence
