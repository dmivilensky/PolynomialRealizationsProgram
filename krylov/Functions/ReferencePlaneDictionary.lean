import krylov.Functions.HilbertPlaneMinimax
import krylov.Tensor.ReferenceLowerBound

/-!
Article: main_krylov, prop:Fcycle(iii), genuine n-atom reference plane.
Use: derive the three planar observed samples and every complete first,
middle and last search line from the original actual CG steps. No planar
trajectory is a source assumption. Source: true CG frame and finite sums.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Reference krylov.Tensor
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual accumulated canonical CG displacement from its first point.
Article: main_krylov, prop:Fcycle(iii). -/
def referencePlaneNode (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (i : ℕ) : EuclideanSpace ℝ (Fin n) := ∑ j∈range i, canonicalCGStep A g j

/-- The real canonical reference has exactly the three printed planar
samples and the true complete first/middle/last lines lie in the two
invisible-cubic hyperplanes. Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlane_sample_lines (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) :
    let N := referenceAtomCount A hA g
    let e := canonicalCGUnitStep A g 0
    let h := canonicalCGUnitStep A g (N-1)
    let p := ‖canonicalCGStep A g 0‖
    let r := ‖canonicalCGStep A g (N-1)‖/p
    0<p ∧ 0<r ∧ ‖e‖=1 ∧ ‖h‖=1 ∧ inner ℝ e h=0 ∧
    (∀ i≤N, (inner ℝ e (referencePlaneNode A g i)=0 ∧ inner ℝ h (referencePlaneNode A g i)=0) ∨
      (inner ℝ e (referencePlaneNode A g i)=p ∧ inner ℝ h (referencePlaneNode A g i)=0) ∨
      (inner ℝ e (referencePlaneNode A g i)=p ∧ inner ℝ h (referencePlaneNode A g i)=r*p)) ∧
    (∀ i<N, (inner ℝ h (referencePlaneNode A g i)=0 ∧ inner ℝ h (canonicalCGStep A g i)=0) ∨
      (inner ℝ e (referencePlaneNode A g i)=p ∧ inner ℝ e (canonicalCGStep A g i)=0)) := by
  let N := referenceAtomCount A hA g
  let e := canonicalCGUnitStep A g 0
  let h := canonicalCGUnitStep A g (N-1)
  let p := ‖canonicalCGStep A g 0‖
  let r := ‖canonicalCGStep A g (N-1)‖/p
  let i0 : Fin N := ⟨0,by omega⟩
  let il : Fin N := ⟨N-1,by omega⟩
  have hframe := canonicalCG_frame A hA g
  have he := hframe.norm_eq_one i0
  have hh := hframe.norm_eq_one il
  have heh := hframe.inner_eq_zero (show i0≠il by intro hz; have := congrArg Fin.val hz; dsimp only [i0,il] at this; omega)
  change ‖e‖=1 at he
  change ‖h‖=1 at hh
  change inner ℝ e h=0 at heh
  have hp : 0<p := norm_pos_iff.mpr (canonicalCGStep_ne_zero A hA g 0
    (fun j hj => cg_nonstagnation A hA g j (by omega)))
  have hv : 0<‖canonicalCGStep A g (N-1)‖ := norm_pos_iff.mpr (canonicalCGStep_ne_zero A hA g (N-1)
    (fun j hj => cg_nonstagnation A hA g j (by omega)))
  have hr : 0<r := div_pos hv hp
  have hpr : r*p=‖canonicalCGStep A g (N-1)‖ := div_mul_cancel₀ _ hp.ne'
  have hφ (i : ℕ) (hi : i<N) : inner ℝ e (canonicalCGStep A g i)=if i=0 then p else 0 := by
    have hs := canonical_step_unit_pair A hA g i0 ⟨i,hi⟩
    change inner ℝ e (canonicalCGStep A g i)=(if i0=(⟨i,hi⟩ : Fin N) then ‖canonicalCGStep A g i‖ else 0) at hs
    by_cases hz : i=0
    · subst i
      simpa only [i0,ite_true] using hs
    · simpa only [Fin.ext_iff,i0,show ¬(0:ℕ)=i by omega,hz,ite_false] using hs
  have hψ (i : ℕ) (hi : i<N) : inner ℝ h (canonicalCGStep A g i)=if i+1=N then r*p else 0 := by
    have hs := canonical_step_unit_pair A hA g il ⟨i,hi⟩
    change inner ℝ h (canonicalCGStep A g i)=(if il=(⟨i,hi⟩ : Fin N) then ‖canonicalCGStep A g i‖ else 0) at hs
    by_cases hz : i+1=N
    · have hi' : i=N-1 := by omega
      simpa only [Fin.ext_iff,il,hi',show N-1+1=N by omega,ite_true,hpr] using hs
    · simpa only [Fin.ext_iff,il,show ¬N-1=i by omega,hz,ite_false] using hs
  have hcoords (i : ℕ) (hi : i≤N) := valueFibre_coordinates_of_steps N (by omega)
    (referencePlaneNode A g) (canonicalCGStep A g) (innerSL ℝ e) (innerSL ℝ h) p r
    (fun j _ => Finset.sum_range_succ _ j) hφ hψ hi
  have hc (i : ℕ) (hi : i≤N) :
      inner ℝ e (referencePlaneNode A g i)=(if i=0 then 0 else p) ∧
      inner ℝ h (referencePlaneNode A g i)=(if i=N then r*p else 0) := by
    simpa only [referencePlaneNode,range_zero,sum_empty,sub_zero,innerSL_apply_apply] using hcoords i hi
  refine ⟨hp,hr,he,hh,heh,?_,?_⟩
  · intro i hi
    by_cases hi0 : i=0
    · left
      simpa only [hi0,ite_true,show ¬(0:ℕ)=N by omega,ite_false] using hc i hi
    · by_cases hiN : i=N
      · right; right
        simpa only [hiN,show N≠0 by omega,ite_false,ite_true] using hc i hi
      · right; left
        simpa only [hi0,hiN,ite_false] using hc i hi
  · intro i hi
    by_cases hilast : i+1=N
    · right
      have hi0 : i≠0 := by omega
      exact ⟨by simpa only [hi0,ite_false] using (hc i hi.le).1,
        by simpa only [hi0,ite_false] using hφ i hi⟩
    · left
      exact ⟨by simpa only [show i≠N by omega,ite_false] using (hc i hi.le).2,
        by simpa only [hilast,ite_false] using hψ i hi⟩

end
end krylov.Functions
