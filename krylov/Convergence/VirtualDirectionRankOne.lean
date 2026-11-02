import krylov.Convergence.VirtualRankOneCoefficient
import krylov.Convergence.VirtualDirectionMidpoints

/-!
Article: main_krylov, prop:EL, direction-basis exact rank-one forgetting.
Use: compute the printed original relative-trial product without an oblique
factor for the genuine compatible third tensor. Source: exact equality of
quadratic histories and true direction-basis midpoint contractions.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
  krylov.Tensor krylov.Correction krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Only the first compatible cubic slice survives in the direction basis.
Article: prop:EL, the printed virtual-forgetting comparison. -/
theorem xrfcDTensorCoefficient_rankOne
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) (M : ℝ)
    (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ a b c,(rankOneCubic (canonicalCGUnitStep base (cgOperator base u) 0) M).form
      (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c) :
    xrfcDTensorCoefficient trial base D u=
      (xrfcTrialCoefficient trial base (cgOperator base u) n 0*M*
        Real.sqrt (cgEnergy base (cgOperator base u) 0)/2) •
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
  have hpre i (hi : i<n):=cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hhist:=xrfc_quadratic_basis_histories trial (cgOperator base)
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g n hpre
    (fun i hi=>(ht i hi).ne')
  have htD i (hi : i<n): trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) g i)≠0 := by
    rw [hhist i hi.le]
    exact (ht i hi).ne'
  have hm l:=xrfcDReferenceMidpointDrift_eq_step trial base hb u hc htD l
  change xrfcDirectionResponse trial base g _=_
  unfold xrfcDirectionResponse
  simp only [hm]
  simp only [hslice]
  rw [sum_eq_single 0]
  · rw [canonicalVariation_rankOneCubic_apply,hpair 0 hn,ite_eq_left rfl,mul_one,
      xrfc_midpoint_first_first trial base hb u hc hn ht,smul_smul]
    congr 1
    ring
  · intro b hb hne
    rw [canonicalVariation_rankOneCubic_apply,hpair b (mem_range.mp hb),ite_eq_right hne,
      mul_zero,zero_smul,smul_zero]
  · intro hnot
    exact (hnot (mem_range.mpr hn)).elim

/-- The direction basis has the exact same forgetting product with no oblique factor.
Article: main_krylov, prop:EL. -/
theorem xrfcDTensorCoefficient_rankOne_norm
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) (M : ℝ) (hM : 0≤M)
    (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ a b c,(rankOneCubic (canonicalCGUnitStep base (cgOperator base u) 0) M).form
      (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c) :
    let g := cgOperator base u
    let τ := fun i=>trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) g i)
    ‖xrfcDTensorCoefficient trial base D u‖=
      M/2*|1-τ 0/CG.length (cgOperator base) g 0| *
        (∏ i∈Ico 1 n,|(CG.length (cgOperator base) g i-τ i)/τ i|)*
        cgEnergy base g 0 := by
  dsimp only
  rw [xrfcDTensorCoefficient_rankOne trial base hb D u M hc hn ht hT,norm_smul,Real.norm_eq_abs,
    abs_div,abs_mul,abs_mul,abs_of_nonneg hM,abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (by norm_num : (0:ℝ)≤2),
    (canonicalCG_frame_of_full_atoms base hb (cgOperator base u) hc).norm_eq_one ⟨0,hn⟩,mul_one,
    xrfc_trial_coefficient_abs trial base hb (cgOperator base u) n 0 (by rw [hc];exact hn)]
  have hsq : Real.sqrt (cgEnergy base (cgOperator base u) 0)^2=cgEnergy base (cgOperator base u) 0 :=
    Real.sq_sqrt ((cgEnergy_pos base hb (cgOperator base u) 0 (by rw [hc];exact hn)).le)
  calc
    _ = M/2*|1-trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) 0)/
        CG.length (cgOperator base) (cgOperator base u) 0| *
      (∏ i∈Ico 1 n,|(CG.length (cgOperator base) (cgOperator base u) i-
        trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))/
        trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)|)*
      (Real.sqrt (cgEnergy base (cgOperator base u) 0))^2 := by ring
    _ = _ := by rw [hsq]

/-- The same printed product reads only the actual direction-basis trial
histories, under that basis's original positivity assumption. Article: prop:EL. -/
theorem xrfcDTensorCoefficient_rankOne_norm_of_direction
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : E →L[ℝ] E →L[ℝ] E) (u : E) (M : ℝ) (hM : 0≤M)
    (hc : referenceAtomCount base hb (cgOperator base u)=n) (hn : 0<n)
    (ht : ∀ i<n,0<trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ a b c,(rankOneCubic (canonicalCGUnitStep base (cgOperator base u) 0) M).form
      (cgOperator (metricRoot base) a) (cgOperator (metricRoot base) b)
      (cgOperator (metricRoot base) c)=inner ℝ (D a b) c) :
    let g := cgOperator base u
    let τ := fun i=>trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) g i)
    ‖xrfcDTensorCoefficient trial base D u‖=
      M/2*|1-τ 0/CG.length (cgOperator base) g 0| *
        (∏ i∈Ico 1 n,|(CG.length (cgOperator base) g i-τ i)/τ i|)*
        cgEnergy base g 0 := by
  let g:=cgOperator base u
  have hpre i (hi : i<n):=cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hhist:=xrfc_quadratic_basis_histories_of_direction trial (cgOperator base)
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g n hpre
    (fun i hi=>(ht i hi).ne')
  have hS i (hi : i<n):0<trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) g i) := by
    rw [←hhist i hi.le]
    exact ht i hi
  have hh:=xrfcDTensorCoefficient_rankOne_norm trial base hb D u M hM hc hn hS hT
  dsimp only at hh ⊢
  have hτ i (hi : i<n) : trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)=
      trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i) :=
    congrArg trial (hhist i hi.le).symm
  have hprod : (∏ i∈Ico 1 n,|(CG.length (cgOperator base) (cgOperator base u) i-
      trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))/
      trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)|)=
      ∏ i∈Ico 1 n,|(CG.length (cgOperator base) (cgOperator base u) i-
      trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))/
      trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)| := by
    apply prod_congr rfl
    intro i hi
    rw [hτ i (mem_Ico.mp hi).2]
  rwa [hτ 0 hn,hprod] at hh

end
end krylov.Convergence
