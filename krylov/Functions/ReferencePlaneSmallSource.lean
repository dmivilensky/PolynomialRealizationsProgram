import krylov.Functions.ReferencePlaneNativePrefix
import krylov.Correction.ResponseHomogeneity

/-!
Article: main_krylov, prop:Fcycle(iii), genuine small-cycle source domain.
Use: derive the common positive search ball and all reference-node admission
conditions for the actual scaled full-reference scalar family. Source:
true CG homogeneity and the proved actual uniform cubic Hessian bound.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Methods krylov.Stability krylov.Correction
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual full reference plane remains unchanged by positive source
scaling. Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneFirst_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) :
    referencePlaneFirst A (ε • g)=referencePlaneFirst A g :=
  canonicalCGUnitStep_positive_scalar A hA g hε 0

/-- The true final active reference plane direction also remains unchanged.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneLast_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) :
    referencePlaneLast A hA (ε • g)=referencePlaneLast A hA g := by
  rw [referencePlaneLast,referenceAtomCount_scalar A hA g ε hε.ne',canonicalCGUnitStep_positive_scalar A hA g hε]
  rfl

/-- The actual first-step norm scales with the genuine physical source.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneFirstLength_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) :
    ‖canonicalCGStep A (ε • g) 0‖=ε*‖canonicalCGStep A g 0‖ := by
  rw [canonicalCGStep_scalar A hA g ε hε.ne',norm_smul,Real.norm_of_nonneg hε.le]

/-- The true printed last/first reference ratio is exactly unchanged by
positive physical source scaling. Article: prop:Fcycle(iii). -/
theorem referencePlaneRatio_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) :
    referencePlaneRatio A hA (ε • g)=referencePlaneRatio A hA g := by
  rw [referencePlaneRatio,referenceAtomCount_scalar A hA g ε hε.ne',
    canonicalCGStep_scalar A hA g ε hε.ne',referencePlaneFirstLength_scalar A hA g hε,
    norm_smul,Real.norm_of_nonneg hε.le,mul_div_mul_left _ _ hε.ne']
  rfl

/-- Every actual canonical reference node has its true homogeneous source
scaling. Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneNode_scalar (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) {ε : ℝ} (hε : 0<ε) (i : ℕ) :
    referencePlaneNode A (ε • g) i=ε • referencePlaneNode A g i := by
  simp only [referencePlaneNode,canonicalCGStep_scalar A hA g ε hε.ne',smul_sum]

set_option maxHeartbeats 800000 in
/-- Primitive actual source cubics admit one common positive search ball
and all their actual quadratic-reference nodes lie inside it, uniformly
over bounded tensor shrinks and the entire genuine binary ball.
The source has no supplied trajectory/query conditions.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlane_small_source_domain (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (U : ℝ) (hU : 0<U) :
    ∃ R ep : ℝ, 0<R ∧ 0<ep ∧ ∀ ε : ℝ, 0<ε → ε<ep → ∀ α : ℝ, 0≤α → α≤U →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
        ReferencePlanePositiveBall A hA (ε • g) (scaleBinaryCubic α t) R ∧
        ∀ i≤referenceAtomCount A hA (ε • g), ‖referencePlaneNode A (ε • g) i‖≤R := by
  obtain ⟨_,_,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
  change ‖referencePlaneFirst A g‖=1 at he
  change ‖referencePlaneLast A hA g‖=1 at hh
  change inner ℝ (referencePlaneFirst A g) (referencePlaneLast A hA g)=0 at heh
  obtain ⟨R,ep,hR,hep,hH⟩ := hilbertPlaneHessian_uniform_positive_ball (referencePlaneFirst A g)
    (referencePlaneLast A hA g) he hh heh (referencePlaneRatio A hA g) U hU
  let N := referenceAtomCount A hA g
  let D := (∑ i∈range (N+1), ‖referencePlaneNode A g i‖)+1
  have hD : 0<D := by
    have hs : 0≤∑ i∈range (N+1), ‖referencePlaneNode A g i‖ := sum_nonneg (fun i _=>norm_nonneg _)
    dsimp only [D]
    linarith only [hs]
  have hb i (hi : i≤N) : ‖referencePlaneNode A g i‖≤D := by
    have hh := single_le_sum (f:=fun i=>‖referencePlaneNode A g i‖)
      (fun i _ => norm_nonneg _) (mem_range.mpr (by omega : i<N+1))
    exact hh.trans (by dsimp only [D]; linarith)
  let e₀ := min (ep/(‖canonicalCGStep A g 0‖+1)) (R/(D+1))
  have hn1 : 0<‖canonicalCGStep A g 0‖+1 := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  have hD1 : 0<D+1 := add_pos hD zero_lt_one
  refine ⟨R,e₀,hR,lt_min (div_pos hep hn1) (div_pos hR hD1),?_⟩
  intro ε hε heps α hα hαU t ht
  have hp : 0<ε*‖canonicalCGStep A g 0‖ := by
    have hn := norm_pos_iff.mpr (canonicalCGStep_ne_zero A hA g 0
      (fun i hi=>cg_nonstagnation A hA g i (by omega)))
    exact mul_pos hε hn
  have hpsmall : ε*‖canonicalCGStep A g 0‖<ep := by
    have hh := (lt_div_iff₀ hn1).mp
      (heps.trans_le (min_le_left _ _))
    nlinarith only [hh,hε]
  constructor
  · intro z hz v
    simpa only [referencePlaneFirst_scalar A hA g hε,referencePlaneLast_scalar A hA g hε,
      referencePlaneFirstLength_scalar A hA g hε,referencePlaneRatio_scalar A hA g hε] using
      hH (ε*‖canonicalCGStep A g 0‖) hp hpsmall α hα hαU t ht z hz v
  · intro i hi
    rw [referenceAtomCount_scalar A hA g ε hε.ne'] at hi
    rw [referencePlaneNode_scalar A hA g hε,norm_smul,Real.norm_of_nonneg hε.le]
    have hh := (lt_div_iff₀ hD1).mp (heps.trans_le (min_le_right _ _))
    have hbound := mul_le_mul_of_nonneg_left (hb i hi) hε.le
    nlinarith only [hh,hbound,hε]

end
end krylov.Functions
