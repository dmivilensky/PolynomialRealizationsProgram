import krylov.Functions.HilbertPlaneRFCFReduction
import krylov.Functions.ReferencePlaneStationarity

/-!
Article: main_krylov, thm:Fplanar, actual CG geometry for the full RFC-F solve.
Use: discharge all finite first/middle/last window conditions directly from
the genuine active CG frame, without a prescribed window or model block.
Source: actual CG orthonormal steps and exact finite displacement sums.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Methods krylov.Correction krylov.Reference krylov.Tensor
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n k : ℕ}

set_option maxHeartbeats 1200000 in
/-- The real full active CG step window supplies precisely the geometry
used in the proved actual full-model reduction.
Article: main_krylov, thm:Fplanar, no window geometry is assumed. -/
theorem referencePlaneRFCF_window_geometry
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount A hA g=k+2) :
    let e := referencePlaneFirst A g
    let h := referencePlaneLast A hA g
    let m := referencePlaneComplement A hA g
    let p := ‖canonicalCGStep A g 0‖
    let r := referencePlaneRatio A hA g
    let a := fun i : Fin (k+2)=>referencePlaneNode A g i.val
    let s := fun i : Fin (k+2)=>canonicalCGStep A g i.val
    (∀ i, hilbertPlaneProject e h (a i)=planeRFCFWindowAnchor p i) ∧
    (∀ i, hilbertPlaneProject e h (s i)=planeRFCFWindowStep p r i) ∧
    s ⊥=p • e ∧ s ⊤=(r*p) • h ∧ LinearIndependent ℝ s ∧
    (∀ i, inner ℝ (s i) (hilbertPlaneTerminal e h m p r-a i)=‖s i‖^2) ∧
    hilbertPlaneTerminal e h m p r=a ⊤+s ⊤ := by
  dsimp only
  let N := referenceAtomCount A hA g
  let e := referencePlaneFirst A g
  let h := referencePlaneLast A hA g
  let m := referencePlaneComplement A hA g
  let p := ‖canonicalCGStep A g 0‖
  let r := referencePlaneRatio A hA g
  let a := fun i : Fin (k+2)=>referencePlaneNode A g i.val
  let s := fun i : Fin (k+2)=>canonicalCGStep A g i.val
  have hbot : (⊥ : Fin (k+2)).val=0 := rfl
  have htop : (⊤ : Fin (k+2)).val=k+1 := by change k+2-1=k+1; omega
  have hN : 2≤referenceAtomCount A hA g := by omega
  have hp : 0<p := (referencePlane_sample_lines A hA g hN).1
  have hpr : r*p=‖canonicalCGStep A g (k+1)‖ := by
    dsimp only [r,referencePlaneRatio,p]
    rw [hc,show k+2-1=k+1 by omega,div_mul_cancel₀ _ hp.ne']
  have hhl : h=canonicalCGUnitStep A g (k+1) := by dsimp only [h,referencePlaneLast]; rw [hc]; congr 1
  have hcoord0 (i : Fin (k+2)) : inner ℝ e (a i)=if i=⊥ then 0 else p := by
    have ht := referencePlaneNode_unit_coordinate A hA g ⟨0,by omega⟩ i.val (by omega)
    change inner ℝ e (a i)=(if 0 < i.val then p else 0) at ht
    by_cases hi : i=⊥
    · simpa [hi] using ht
    · have hv : 0 < i.val := by
        have hh : i.val≠0 := by simpa only [Fin.ext_iff,hbot] using hi
        omega
      simpa only [ite_eq_left hv,ite_eq_right hi] using ht
  have hcoord1 (i : Fin (k+2)) : inner ℝ h (a i)=0 := by
    rw [hhl]
    have ht := referencePlaneNode_unit_coordinate A hA g ⟨k+1,by omega⟩ i.val (by omega)
    change inner ℝ (canonicalCGUnitStep A g (k+1)) (a i)=_ at ht
    simpa only [ite_eq_right (by omega : ¬(k+1 < i.val))] using ht
  have hsteps0 (i : Fin (k+2)) : inner ℝ e (s i)=if i=⊥ then p else 0 := by
    have ht := canonical_step_unit_pair A hA g (⟨0,by omega⟩ : Fin N) (⟨i.val,by omega⟩ : Fin N)
    change inner ℝ e (s i)=(if (⟨0,by omega⟩ : Fin N)=⟨i.val,by omega⟩ then ‖s i‖ else 0) at ht
    by_cases hi : i=⊥
    · subst i
      simpa only [s,p,hbot,ite_true] using ht
    · have hi0 : (0:ℕ)≠i.val := by
        have hh : i.val≠0 := by simpa only [Fin.ext_iff,hbot] using hi
        omega
      have ht' : inner ℝ e (s i)=0 := by simpa only [Fin.ext_iff,ite_eq_right hi0] using ht
      simpa only [ite_eq_right hi] using ht'
  have hsteps1 (i : Fin (k+2)) : inner ℝ h (s i)=if i=⊤ then r*p else 0 := by
    rw [hhl]
    have ht := canonical_step_unit_pair A hA g (⟨k+1,by omega⟩ : Fin N) (⟨i.val,by omega⟩ : Fin N)
    change inner ℝ (canonicalCGUnitStep A g (k+1)) (s i)=
      (if (⟨k+1,by omega⟩ : Fin N)=⟨i.val,by omega⟩ then ‖s i‖ else 0) at ht
    by_cases hi : i=⊤
    · subst i
      simpa only [s,htop,Fin.ext_iff,hpr,ite_true] using ht
    · have hiv : i.val≠k+1 := by simpa only [Fin.ext_iff,htop] using hi
      have hne : k+1≠i.val := Ne.symm hiv
      have ht' : inner ℝ h (s i)=0 := by
        rw [hhl]
        simpa only [Fin.ext_iff,ite_eq_right hne] using ht
      simpa only [ite_eq_right hi,hhl] using ht'
  have ha (i : Fin (k+2)) : hilbertPlaneProject e h (a i)=planeRFCFWindowAnchor p i := by
    rw [hilbertPlaneProject_apply,hcoord0,hcoord1]
    by_cases hi : i=⊥
    · simp only [ite_eq_left hi,planeRFCFWindowAnchor]
      ext j
      fin_cases j <;> rfl
    · simp only [ite_eq_right hi,planeRFCFWindowAnchor]
  have hs (i : Fin (k+2)) : hilbertPlaneProject e h (s i)=planeRFCFWindowStep p r i := by
    rw [hilbertPlaneProject_apply,hsteps0,hsteps1]
    by_cases hi0 : i=⊥ <;> by_cases hi1 : i=⊤ <;>
      simp_all [planeRFCFWindowStep]
    ext j
    fin_cases j <;> rfl
  have hfirst : s ⊥=p • e := (NormedSpace.norm_smul_normalize _).symm
  have hlaststep : s ⊤=(r*p) • h := by
    rw [hpr,hhl]
    exact (NormedSpace.norm_smul_normalize _).symm
  have hind : LinearIndependent ℝ s := by
    have hf := canonicalCG_frame A hA g
    rw [hc] at hf
    have hn i : ‖s i‖≠0 := norm_ne_zero_iff.mpr (canonicalCGStep_ne_zero A hA g i.val
      (fun j hj=>cg_nonstagnation A hA g j (by have hh := i.isLt; omega)))
    have ht := hf.linearIndependent.units_smul (fun i=>Units.mk0 ‖s i‖ (hn i))
    convert ht using 1
    funext i
    exact (NormedSpace.norm_smul_normalize _).symm
  have hz : hilbertPlaneTerminal e h m p r=referencePlaneNode A g N := referencePlaneTerminal_eq_node A hA g
  have hfuture (i : Fin (k+2)) : inner ℝ (s i) (hilbertPlaneTerminal e h m p r-a i)=‖s i‖^2 := by
    have hsi : s i=‖s i‖ • canonicalCGUnitStep A g i.val := (NormedSpace.norm_smul_normalize _).symm
    have h0 := referencePlaneNode_unit_coordinate A hA g ⟨i.val,by omega⟩ i.val (by omega)
    have h1 := referencePlaneNode_unit_coordinate A hA g ⟨i.val,by omega⟩ N le_rfl
    have hiN : i.val<N := by dsimp only [N]; have hh := i.isLt; omega
    simp only [lt_self_iff_false,ite_false] at h0
    simp only [ite_eq_left hiN] at h1
    change inner ℝ (canonicalCGUnitStep A g i.val) (a i)=0 at h0
    change inner ℝ (canonicalCGUnitStep A g i.val) (referencePlaneNode A g N)=‖s i‖ at h1
    rw [hz]
    conv_lhs => rw [hsi,real_inner_smul_left,inner_sub_right,h0,h1]
    ring
  have hlast : hilbertPlaneTerminal e h m p r=a ⊤+s ⊤ := by
    rw [hz]
    change referencePlaneNode A g N=referencePlaneNode A g (k+1)+canonicalCGStep A g (k+1)
    rw [show N=k+1+1 by dsimp only [N]; omega]
    exact Finset.sum_range_succ _ _
  exact ⟨ha,hs,hfirst,hlaststep,hind,hfuture,hlast⟩

end
end krylov.Functions
