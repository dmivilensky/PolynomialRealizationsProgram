import krylov.Information.QueryBasis

/-!
Article: main_krylov, thm:C2(c), the actual observed-query normal tube.
Use: genuine original finite RFC scenarios determine the real unobserved
unit normal, its first-order displacement, full inverse domain and exact
orthogonality to all actual observed later query directions.
Source: actual raw RFC query-basis analyticity and independently proved
full CG reference rank, with exact inverse-transpose covector transport.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
/-- The actual source unobserved unit normal constructed from the genuine raw query matrix and its true CG reference matrix.
Use: the informed data-only consistency fibre uses the actual moving observed later-query hyperplane.
Article: main_krylov, thm:C2(c), genuine moving v₀. -/
def sourceUnobservedNormal {N : ℕ} (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) (Θ : symmetricScenarios (N+1) (N+1)) :
    EuclideanSpace ℝ (Fin (N+1)) :=
  transportedUnitNormal (sourceQueryMatrix base g Θ) (sourceQueryMatrix base g 0) (canonicalCGUnitStep base g 0)

/-- The actual source unobserved normal has a genuine first-order displacement from the true first CG unit step, with no supplied geometric estimate.
Use: discharge the normal-displacement term in the genuine primitive-budget midpoint coefficient.
Article: main_krylov, thm:C2(c), actual v₀=ŝ₀+O(ω).
Proof: the actual source query matrix is jointly analytic and its true
reference determinant is a unit by actual CG geometry. Apply the proved
inverse-transpose transported-normal theorem with the genuine unit first step.
-/
theorem sourceUnobservedNormal_order {N : ℕ}
    (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount base hb g=N+1) :
    (fun Θ : symmetricScenarios (N+1) (N+1) =>
      sourceUnobservedNormal base g Θ-canonicalCGUnitStep base g 0) =O[𝓝 0] (fun Θ => ‖Θ‖) := by
  have hf := canonicalCG_frame_of_full_atoms base hb g hcount
  have he : ‖canonicalCGUnitStep base g 0‖=1 := by simpa only [Fin.val_zero] using hf.norm_eq_one (0 : Fin (N+1))
  exact transportedUnitNormal_order (sourceQueryMatrix base g) (sourceQueryMatrix_entry_analytic base hb g hcount)
    (sourceQueryMatrix_reference_unit base hb g hcount) _ he

/-- One genuine finite-source tube makes the actual raw query matrix invertible, the actual unobserved normal unit and its reference displacement uniformly first order.
Use: all normal and inverse-domain constants precede every original perturbation scenario and budget profile.
Article: main_krylov, thm:C2(c), actual all-scenario moving observed-hyperplane control.
Proof: the genuine query-basis regularity and actual reference rank give
one real neighborhood with all inverse and normalization domains. Intersect
it with the proved actual normal-displacement bound and shrink to one
closed source ball. No midpoint-selector regularity is assumed.
-/
theorem sourceUnobservedNormal_tube {N : ℕ}
    (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount base hb g=N+1) :
    ∃ δ L : ℝ, 0<δ ∧ 0<L ∧ ∀ Θ : symmetricScenarios (N+1) (N+1), ‖Θ‖≤δ →
      IsUnit (sourceQueryMatrix base g Θ).det ∧ ‖sourceUnobservedNormal base g Θ‖=1 ∧
        ‖sourceUnobservedNormal base g Θ-canonicalCGUnitStep base g 0‖≤L*‖Θ‖ := by
  -- Actual full CG data determine the common inverse/normalization neighborhood before every source scenario.
  have hf := canonicalCG_frame_of_full_atoms base hb g hcount
  have he : ‖canonicalCGUnitStep base g 0‖=1 := by simpa only [Fin.val_zero] using hf.norm_eq_one (0 : Fin (N+1))
  have hd := transportedUnitNormal_domains (sourceQueryMatrix base g) (sourceQueryMatrix_entry_analytic base hb g hcount)
    (sourceQueryMatrix_reference_unit base hb g hcount) _ he
  obtain ⟨L,hL,hbound⟩ := isBigO_iff'.mp (sourceUnobservedNormal_order base hb g hcount)
  obtain ⟨ε,hε,hεbound⟩ := Metric.eventually_nhds_iff.mp (hd.and hbound)
  refine ⟨ε/2,L,half_pos hε,hL,?_⟩
  intro Θ hΘ
  have ht := hεbound (by simpa only [dist_zero_right] using hΘ.trans_lt (half_lt_self hε))
  exact ⟨ht.1.1,ht.1.2.2,by simpa only [norm_norm] using ht.2⟩


/-- The genuinely computed moving unit normal is perpendicular to every actual later RFC query, on the true current query-basis inverse domain.
Use: the known-base consistency fibre is formed from the original observed later-query hyperplane of the actual executor.
Article: main_krylov, thm:C2(c), v₀⊥span{A¹ᐟ²d₁,…,A¹ᐟ²d_(n−1)}.
Proof: exact inverse-transpose transport preserves the actual reference
covector on all genuine query columns. Their true later reference pairings
with the first CG unit step vanish. Unit normalization preserves each zero
pairing, without assuming any abstract observed subspace or normal.
-/
theorem sourceUnobservedNormal_orthogonal {N : ℕ}
    (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount base hb g=N+1)
    (Θ : symmetricScenarios (N+1) (N+1)) (hu : IsUnit (sourceQueryMatrix base g Θ).det)
    (i : Fin (N+1)) (hi : i.val<N) :
    inner ℝ (sourceUnobservedNormal base g Θ) (sourceQueryColumns base g Θ i)=0 := by
  -- Preserve the same true reference covector before normalizing the actual transported normal.
  let C := sourceQueryMatrix base g Θ
  let C₀ := sourceQueryMatrix base g 0
  let e := canonicalCGUnitStep base g 0
  let w := transportedNormal C C₀ e
  have ht : IsUnit Cᵀ.det := by simpa only [det_transpose] using hu
  have hc : cgOperator Cᵀ w=cgOperator C₀ᵀ e := by
    simp only [w,transportedNormal,cgOperator,← mul_apply_eq_comp,← map_mul,← Matrix.mul_assoc,
      mul_nonsing_inv _ ht,Matrix.one_mul]
  have hp : projectedResidual (sourceQueryColumns base g Θ) w=projectedResidual (sourceQueryColumns base g 0) e := by
    rw [projectedResidual_fullBasisMatrix,projectedResidual_fullBasisMatrix]
    exact hc
  have hpair : inner ℝ (sourceQueryColumns base g Θ i) w=0 :=
    (congrArg (fun v : EuclideanSpace ℝ (Fin (N+1)) => v i) hp).trans
      (sourceQueryColumns_reference_orthogonal base hb g hcount i hi)
  have hw : inner ℝ w (sourceQueryColumns base g Θ i)=0 :=
    (real_inner_comm (sourceQueryColumns base g Θ i) w).trans hpair
  change inner ℝ (NormedSpace.normalize w) (sourceQueryColumns base g Θ i)=0
  simp only [NormedSpace.normalize,real_inner_smul_left,hw,mul_zero]

end
end krylov.Information
