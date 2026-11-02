import krylov.Methods.NazarethProjection
import Mathlib.Tactic.FinCases
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(a), exact original Lanczos next direction.
Use: prove the literal three-term direction on the actual last two scaled
CG directions, with all inverse and independence domains derived.
Source: Nazareth77 equation (10), the genuine diagonal observed projection
and actual CG recurrences; arbitrary positive direction scales are retained. -/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal original first Lanczos recurrence produces the next true CG
direction scaled by the actual old direction scale over its true CG length.
Use: initialize the real arbitrary-trial Nazareth execution induction.
Article: main_krylov, prop:classical(a), Nazareth77 equation (10).
Proof: the actual singleton direction is independent and spans the initial
residual. The genuine diagonal scalar projection is its real solve; actual
CG recurrence uniqueness identifies its resulting next direction. -/
theorem nazareth_first_cg_step (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (hg : g≠0)
    (scale : ℝ) (hscale : scale≠0) :
    let t := scale • CG.direction Q g 0
    show Prop from -Q t+(inner ℝ (Q t) (Q t)/inner ℝ t (Q t)) • t=
      (scale/CG.length Q g 0) • CG.direction Q g 1 := by
  let t := scale • CG.direction Q g 0
  let s := fun _ : Fin 1 => t
  have ht : t≠0 := smul_ne_zero hscale (neg_ne_zero.mpr hg)
  have hLI : LinearIndependent ℝ s := linearIndependent_unique_iff.mpr ht
  have ha : inner ℝ t (Q t)≠0 := (hpos t ht).ne'
  have hG : crossGram (fun i => Q (s i)) s=diagonal (fun _ => inner ℝ t (Q t)) := by
    ext i j
    fin_cases i
    fin_cases j
    simp only [Matrix.diagonal_apply_eq]
    exact real_inner_comm _ _
  have hdiag := conjugacyDirection_diagonal s (fun i => Q (s i)) (Q t) _ (fun _ => ha) hG
  have htmem : t∈Submodule.span ℝ (Set.range s) := Submodule.subset_span ⟨0,rfl⟩
  have hd : CG.direction Q g 0∈Submodule.span ℝ (Set.range s) := by
    simpa only [t,smul_smul,inv_mul_cancel₀ hscale,one_smul] using
      Submodule.smul_mem (Submodule.span ℝ (Set.range s)) scale⁻¹ htmem
  have hgrad : CG.gradient Q g 0∈Submodule.span ℝ (Set.range s) := by
    simpa only [CG.direction,CG.gradient,cgRun,neg_neg] using Submodule.neg_mem _ hd
  have hpre0 : ∀ i<0+1,CG.gradient Q g i≠0 := by
    intro i hi
    have he : i=0 := by omega
    subst i
    exact hg
  have hp := cg_next_probe_projection Q hQ hpos g 0 hpre0
    s hLI (fun _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨0,by change 0<1;omega,rfl⟩)) hd hgrad scale
  rw [hdiag] at hp
  simpa only [Fin.sum_univ_one,s] using hp

/-- The literal original three-term Lanczos recurrence on the actual last
two positively scaled CG directions gives precisely the next CG direction,
scaled by the newest direction scale divided by its actual exact CG length.
Use: the original arbitrary positive trial schedule preserves genuine
positive CG direction multiples; no leading-Krylov coefficient is assumed.
Article: main_krylov, prop:classical(a), Nazareth77 equation (10).
Proof: true CG conjugacy and positive curvature derive independence and both
actual scalar energy domains. Its two last directions contain the current
residual by the genuine recurrence. The proved diagonal observed projection
and actual next-image solve give the literal three displayed terms. -/
theorem nazareth_three_term_cg_step (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i<k+2,CG.gradient Q g i≠0)
    (scale oldScale : ℝ) (hscale : scale≠0) (hold : oldScale≠0) :
    let t := scale • CG.direction Q g (k+1)
    let old := oldScale • CG.direction Q g k
    show Prop from -Q t+(inner ℝ (Q t) (Q t)/inner ℝ t (Q t)) • t+
      (inner ℝ (Q old) (Q t)/inner ℝ old (Q old)) • old=
        (scale/CG.length Q g (k+1)) • CG.direction Q g (k+2) := by
  let t := scale • CG.direction Q g (k+1)
  let old := oldScale • CG.direction Q g k
  let s : Fin 2 → E := ![t,old]
  have hInv := CG.invariant Q hQ hpos g (k+2) hpre
  have hc : inner ℝ (CG.direction Q g k) (Q (CG.direction Q g (k+1)))=0 :=
    hInv.conjugate k (k+1) (by omega) (by omega)
  have hc' : inner ℝ (CG.direction Q g (k+1)) (Q (CG.direction Q g k))=0 := by
    have he := hQ (CG.direction Q g (k+1)) (CG.direction Q g k)
    change inner ℝ (Q (CG.direction Q g (k+1))) (CG.direction Q g k)=
      inner ℝ (CG.direction Q g (k+1)) (Q (CG.direction Q g k)) at he
    exact he.symm.trans ((real_inner_comm _ _).trans hc)
  have hd (j : ℕ) (hj : j<k+2) : CG.direction Q g j≠0 :=
    (CG.invariant_line_pos Q hpos g j (CG.invariant Q hQ hpos g j
      (fun i hi => hpre i (hi.trans hj))) (hpre j hj)).1
  have hs0 (i : Fin 2) : s i≠0 := by
    fin_cases i
    · exact smul_ne_zero hscale (hd (k+1) (by omega))
    · exact smul_ne_zero hold (hd k (by omega))
  have hcross (i j : Fin 2) (hij : i≠j) : inner ℝ (s i) (Q (s j))=0 := by
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · change inner ℝ (scale • CG.direction Q g (k+1)) (Q (oldScale • CG.direction Q g k))=0
      rw [map_smul,real_inner_smul_left,real_inner_smul_right,hc',mul_zero,mul_zero]
    · change inner ℝ (oldScale • CG.direction Q g k) (Q (scale • CG.direction Q g (k+1)))=0
      rw [map_smul,real_inner_smul_left,real_inner_smul_right,hc,mul_zero,mul_zero]
    · exact False.elim (hij rfl)
  have hLI : LinearIndependent ℝ s := conjugate_independent Q hpos s hs0 hcross
  let a := fun i => inner ℝ (s i) (Q (s i))
  have ha (i : Fin 2) : a i≠0 := (hpos _ (hs0 i)).ne'
  have hG : crossGram (fun i => Q (s i)) s=diagonal a := by
    ext i j
    by_cases hij : i=j
    · subst j
      rw [Matrix.diagonal_apply_eq]
      exact real_inner_comm _ _
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact (real_inner_comm _ _).trans (hcross j i (Ne.symm hij))
  have hdmem : CG.direction Q g (k+1)∈Submodule.span ℝ (Set.range s) := by
    have hm : s 0∈Submodule.span ℝ (Set.range s) := Submodule.subset_span ⟨0,rfl⟩
    simpa only [s,Matrix.cons_val_zero,t,smul_smul,inv_mul_cancel₀ hscale,one_smul] using
      Submodule.smul_mem (Submodule.span ℝ (Set.range s)) scale⁻¹ hm
  have homem : CG.direction Q g k∈Submodule.span ℝ (Set.range s) := by
    have hm : s 1∈Submodule.span ℝ (Set.range s) := Submodule.subset_span ⟨1,rfl⟩
    simpa only [s,Matrix.cons_val_one,Matrix.cons_val_zero,old,smul_smul,inv_mul_cancel₀ hold,one_smul] using
      Submodule.smul_mem (Submodule.span ℝ (Set.range s)) oldScale⁻¹ hm
  have hgmem : CG.gradient Q g (k+1)∈Submodule.span ℝ (Set.range s) := by
    have he : CG.gradient Q g (k+1)= -CG.direction Q g (k+1)+CG.beta Q g k • CG.direction Q g k := by
      rw [CG.direction_succ]
      module
    rw [he]
    exact Submodule.add_mem _ (Submodule.neg_mem _ hdmem) (Submodule.smul_mem _ _ homem)
  have hf (i : Fin 2) : s i∈directionFlag Q g (k+2) := by
    fin_cases i
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k+1,by change k+1<k+2;omega,rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,by change k<k+2;omega,rfl⟩)
  have hp := cg_next_probe_projection Q hQ hpos g (k+1) (by simpa only [Nat.add_assoc] using hpre)
    s hLI hf hdmem hgmem scale
  rw [conjugacyDirection_diagonal s (fun i => Q (s i)) (Q t) a ha hG] at hp
  simpa only [Fin.sum_univ_two,s,a,Matrix.cons_val_zero,Matrix.cons_val_one,add_assoc] using hp

end
end krylov.Methods
