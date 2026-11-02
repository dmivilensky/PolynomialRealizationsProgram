import krylov.Methods.VirtualReference
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(a), original Nazareth conjugate Lanczos step.
Use: identify the observed projection of the previous true step image with
a positive next CG direction, using only the original two preceding directions.
Source: Nazareth77, equation (10), as reproduced in main_krylov; actual CG
recurrences and genuine positive conjugacy-solve uniqueness. -/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fintype ι] [DecidableEq ι]

/-- On actual conjugate observed pairs the real conjugacy solve is exactly
the explicit independent scalar projection used by the Lanczos recurrence.
Use: one or two actual stored pairs give the literal Nazareth terms, with
no replacement of the genuine direction by an assumed CG multiple.
Article: main_krylov, prop:classical(a), Nazareth77 equation (10).
Proof: the actual cross-Gram is diagonal with nonzero real energies. The
explicit projected vector has the right old-span displacement and zero
image coordinates, so the original nonsingular solve uniqueness applies. -/
theorem conjugacyDirection_diagonal (s y : ι → E) (g : E)
    (a : ι → ℝ) (ha : ∀ i,a i≠0)
    (hG : crossGram y s=Matrix.diagonal a) :
    conjugacyDirection s y g= -g+∑ i,(inner ℝ (y i) g/a i) • s i := by
  have hinv : IsUnit (crossGram y s).det := by
    rw [hG,Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => ha i))
  apply conjugacyDirection_unique s y g _ hinv
  · convert combine_mem_span s (fun i => inner ℝ (y i) g/a i) using 1
    simp only [combine]
    abel
  · ext i
    change inner ℝ (y i) (-g+combine s (fun i => inner ℝ (y i) g/a i))=0
    rw [inner_add_right,inner_neg_right]
    have he := congrFun (coordinates_combine y s (fun i => inner ℝ (y i) g/a i)) i
    rw [hG,Matrix.mulVec_diagonal] at he
    change inner ℝ (y i) (combine s (fun i => inner ℝ (y i) g/a i))=
      a i*(inner ℝ (y i) g/a i) at he
    rw [he,mul_div_cancel₀ _ (ha i)]
    exact neg_add_cancel _

/-- Projecting the actual previous scaled CG step image against any genuine
independent old window containing its direction and gradient gives exactly
the next CG direction scaled by the previous scale over the true CG length.
Use: the last two conjugate directions suffice in Nazareth's original
three-term recurrence; the scalar is positive for every positive old scale.
Article: main_krylov, prop:classical(a), Nazareth77 equation (10).
Proof: actual CG gradient and direction recurrences put the candidate plus
its actual previous image in the two-direction span. True CG conjugacy
annihilates every observed image, and positive quadratic observations derive
the real inverse domain for the original computed projection. -/
theorem cg_next_probe_projection (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i<k+1,CG.gradient Q g i≠0) (s : ι → E) (hLI : LinearIndependent ℝ s)
    (hflag : ∀ i,s i∈directionFlag Q g (k+1))
    (hd : CG.direction Q g k∈Submodule.span ℝ (Set.range s))
    (hg : CG.gradient Q g k∈Submodule.span ℝ (Set.range s)) (scale : ℝ) :
    conjugacyDirection s (fun i => Q (s i)) (Q (scale • CG.direction Q g k))=
      (scale/CG.length Q g k) • CG.direction Q g (k+1) := by
  have hInv := CG.invariant Q hQ hpos g k (fun i hi => hpre i (by omega))
  have ha := (CG.invariant_line_pos Q hpos g k hInv (hpre k (by omega))).2.1
  have hm := operatorGram_posDef Q hQ hpos hLI
  apply conjugacyDirection_unique s (fun i => Q (s i)) _ _ (isUnit_iff_ne_zero.mpr hm.det_pos.ne')
  · have hrec : CG.direction Q g (k+1)+CG.length Q g k • Q (CG.direction Q g k)=
        CG.beta Q g k • CG.direction Q g k-CG.gradient Q g k := by
      rw [CG.direction_succ,CG.gradient_succ]
      module
    have he : (scale/CG.length Q g k) • CG.direction Q g (k+1)+Q (scale • CG.direction Q g k)=
        (scale/CG.length Q g k) • (CG.beta Q g k • CG.direction Q g k-CG.gradient Q g k) := by
      rw [← hrec,smul_add,smul_smul,div_mul_cancel₀ _ ha.ne',map_smul]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hd) hg)
  · ext i
    change inner ℝ (Q (s i)) ((scale/CG.length Q g k) • CG.direction Q g (k+1))=0
    rw [real_inner_smul_right]
    have hz := directionFlag_conjugate Q hQ hpos g (k+1) hpre (hflag i)
    have he := hQ (s i) (CG.direction Q g (k+1))
    change inner ℝ (Q (s i)) (CG.direction Q g (k+1))=
      inner ℝ (s i) (Q (CG.direction Q g (k+1))) at he
    rw [he,hz,mul_zero]

end
end krylov.Methods
