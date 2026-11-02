import krylov.Functions.ReferencePlaneDictionary
import krylov.Functions.HilbertPlaneSamples
import krylov.Functions.MetricHilbertPlane
import krylov.Reference.Iterates

/-!
Article: main_krylov, prop:Fcycle(iii), original full-reference scalar family.
Use: construct the genuine physical cubic from the actual first/last CG
plane and prove its exact quadratic prefix gradient observations.
Source: true CG step sums, actual termination, and exact scalar sample gradients.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Reference krylov.Tensor krylov.Nonlinear
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual first CG unit direction. Article: prop:Fcycle(iii). -/
def referencePlaneFirst (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :=
  canonicalCGUnitStep A g 0

/-- The actual final active CG unit direction. Article: prop:Fcycle(iii). -/
def referencePlaneLast (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n)) :=
  canonicalCGUnitStep A g (referenceAtomCount A hA g-1)

/-- The actual printed final/first step ratio. Article: prop:Fcycle(iii). -/
def referencePlaneRatio (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖canonicalCGStep A g (referenceAtomCount A hA g-1)‖/‖canonicalCGStep A g 0‖

/-- The true orthogonal-complement displacement of the complete reference.
Article: main_krylov, prop:Fcycle(iii). -/
def referencePlaneComplement (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n)) :=
  referencePlaneNode A g (referenceAtomCount A hA g)-
    hilbertPlaneEmbed (referencePlaneFirst A g) (referencePlaneLast A hA g)
      (planeOfPair (‖canonicalCGStep A g 0‖,referencePlaneRatio A hA g*‖canonicalCGStep A g 0‖))

/-- The actual full n-dimensional physical cubic family of the original
reference, including its true positive metric-root pullback.
Article: main_krylov, prop:Fcycle(iii). -/
def referencePlaneCubicObjective (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (t : krylov.Tensor.BinaryCubic) :=
  metricHilbertPlaneObjective (metricCoordinates A hA) (referencePlaneFirst A g) (referencePlaneLast A hA g)
    (referencePlaneComplement A hA g) ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t

/-- Actual canonical node coordinates are extracted directly from the true
orthogonal CG steps. Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneNode_unit_coordinate (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : Fin (referenceAtomCount A hA g)) (k : ℕ)
    (hk : k≤referenceAtomCount A hA g) :
    inner ℝ (canonicalCGUnitStep A g i.val) (referencePlaneNode A g k)=
      if i.val<k then ‖canonicalCGStep A g i.val‖ else 0 := by
  rw [referencePlaneNode,inner_sum]
  have hp j (hj : j∈range k) := canonical_step_unit_pair A hA g i ⟨j,(mem_range.mp hj).trans_le hk⟩
  by_cases hi : i.val<k
  · rw [ite_eq_left hi,sum_eq_single i.val]
    · simpa only [ite_true] using hp i.val (mem_range.mpr hi)
    · intro j hj hji
      have hij : i≠(⟨j,(mem_range.mp hj).trans_le hk⟩ : Fin (referenceAtomCount A hA g)) := by
        intro hh
        exact hji (congrArg Fin.val hh).symm
      simpa only [ite_eq_right hij] using hp j hj
    · intro hn
      exact (hn (mem_range.mpr hi)).elim
  · rw [ite_eq_right hi]
    apply sum_eq_zero
    intro j hj
    have hij : i≠(⟨j,(mem_range.mp hj).trans_le hk⟩ : Fin (referenceAtomCount A hA g)) := by
      intro hh
      have he := congrArg Fin.val hh
      change i.val=j at he
      have := mem_range.mp hj
      omega
    simpa only [ite_eq_right hij] using hp j hj

/-- The actual canonical displacement is the true root image of the
actual physical CG displacement. Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneNode_metric (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    referencePlaneNode A g i=metricCoordinates A hA (CG.displacement (cgOperator A) g i) := by
  simp only [referencePlaneNode,CG.displacement,map_sum,map_smul]
  apply sum_congr rfl
  intro j _
  rw [canonicalCGStep,cgStep,map_smul,metricCoordinates_apply]
  rfl

/-- Exact genuine CG termination places the common quadratic minimum at
minus the true initial canonical gradient. Article: prop:Fcycle(iii). -/
theorem referencePlaneNode_terminal (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) :
    referencePlaneNode A g (referenceAtomCount A hA g)= -cgCanonicalError A g 0 := by
  have hs := canonicalCGStep_sum A hA g (Nat.zero_le (referenceAtomCount A hA g))
  simpa only [Nat.Ico_zero_eq_range,cgCanonicalError,cg_terminates,map_zero,zero_sub,referencePlaneNode] using hs

/-- The common orthogonal quadratic is truly orthogonal to the actual
first/last reference plane. Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneComplement_project (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) :
    hilbertPlaneProject (referencePlaneFirst A g) (referencePlaneLast A hA g)
      (referencePlaneComplement A hA g)=0 := by
  let N := referenceAtomCount A hA g
  obtain ⟨hp,_,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
  have h0 := referencePlaneNode_unit_coordinate A hA g ⟨0,by omega⟩ N le_rfl
  have hL := referencePlaneNode_unit_coordinate A hA g ⟨N-1,by omega⟩ N le_rfl
  have hcoord : hilbertPlaneProject (referencePlaneFirst A g) (referencePlaneLast A hA g)
      (referencePlaneNode A g N)=planeOfPair (‖canonicalCGStep A g 0‖,
        referencePlaneRatio A hA g*‖canonicalCGStep A g 0‖) := by
    rw [hilbertPlaneProject_apply]
    congr 1
    apply Prod.ext
    · simpa only [referencePlaneFirst,show (0:ℕ)<N by omega,ite_true] using h0
    · simpa only [referencePlaneLast,referencePlaneRatio,show N-1<N by omega,ite_true,
        div_mul_cancel₀ _ hp.ne'] using hL
  change ‖referencePlaneFirst A g‖=1 at he
  change ‖referencePlaneLast A hA g‖=1 at hh
  change inner ℝ (referencePlaneFirst A g) (referencePlaneLast A hA g)=0 at heh
  rw [referencePlaneComplement,map_sub,hilbertPlaneProject_embed _ _ he hh heh,hcoord,sub_self]

/-- Every true first/middle gradient of the physical cubic family is exactly
the genuine original physical quadratic gradient. No reference trajectory
or gradient identity is an assumption. Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneCubicGradient_prefix (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t : krylov.Tensor.BinaryCubic) (i : ℕ) (hi : i<referenceAtomCount A hA g) :
    gradient (referencePlaneCubicObjective A hA g t) (CG.displacement (cgOperator A) g i)=
      CG.gradient (cgOperator A) g i := by
  let S := metricCoordinates A hA
  let N := referenceAtomCount A hA g
  have hS : S.toContinuousLinearMap.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr (krylov.Secant.metricRoot_isSymm A))
  have h0 := referencePlaneNode_unit_coordinate A hA g ⟨0,by omega⟩ i hi.le
  have hL := referencePlaneNode_unit_coordinate A hA g ⟨N-1,by omega⟩ i hi.le
  have hcoords :
      (inner ℝ (referencePlaneFirst A g) (referencePlaneNode A g i)=0 ∧
        inner ℝ (referencePlaneLast A hA g) (referencePlaneNode A g i)=0) ∨
      (inner ℝ (referencePlaneFirst A g) (referencePlaneNode A g i)=‖canonicalCGStep A g 0‖ ∧
        inner ℝ (referencePlaneLast A hA g) (referencePlaneNode A g i)=0) := by
    have hl : inner ℝ (referencePlaneLast A hA g) (referencePlaneNode A g i)=0 := by
      simpa only [referencePlaneLast,show ¬(N-1< i) by omega,ite_false] using hL
    by_cases hi0 : i=0
    · left
      exact ⟨by simpa only [referencePlaneFirst,hi0,lt_self_iff_false,ite_false] using h0,hl⟩
    · right
      exact ⟨by simpa only [referencePlaneFirst,show (0:ℕ)< i by omega,ite_true] using h0,hl⟩
  apply S.symm.injective
  change S.symm (gradient (metricHilbertPlaneObjective S _ _ _ _ _ t) _) = _
  rw [metricHilbertPlaneGradient_normalized S hS,←referencePlaneNode_metric]
  rw [hilbertPlaneGradient_prefix_sample _ _ _ _ _ t _ hcoords]
  have hterm : hilbertPlaneTerminal (referencePlaneFirst A g) (referencePlaneLast A hA g)
      (referencePlaneComplement A hA g) ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g)=referencePlaneNode A g N := by
    dsimp only [hilbertPlaneTerminal,referencePlaneComplement]
    abel
  rw [hterm,referencePlaneNode_terminal]
  have hs := canonicalCGStep_sum A hA g (Nat.zero_le i)
  change (∑ k∈Ico 0 i,canonicalCGStep A g k)=_ at hs
  rw [Nat.Ico_zero_eq_range] at hs
  change referencePlaneNode A g i=cgCanonicalError A g i-cgCanonicalError A g 0 at hs
  rw [hs]
  change cgCanonicalError A g i-cgCanonicalError A g 0- -cgCanonicalError A g 0=cgCanonicalError A g i
  abel

end
end krylov.Functions
