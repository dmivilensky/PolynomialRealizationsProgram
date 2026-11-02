import krylov.Cancellation.DeferredComparison
import krylov.Cancellation.DeferredMinimax
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, literal exhausted-cycle error profile.
Use: express the proved original deferred sharp coefficient, FC improvement
and attained correction-free minimax in the article's genuine last-error norm.
Source: actual terminal CG error telescoping and genuine step energy; the
spatial sharpness, strictness and native method minimax are already proved.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Variation
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- At genuine next-step exhaustion, the true square-root last step energy
is exactly the original last canonical error norm.
Use: identify the printed source coefficient and minimax value literally.
Article: main_krylov, thm:DC.
Proof: the genuine next canonical error is zero; actual error telescoping
makes the last canonical step minus the original last error. -/
theorem last_energy_error_norm (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hstop : referenceAtomCount base hb g≤k+1) :
    Real.sqrt (cgEnergy base g k)=‖cgCanonicalError base g k‖ := by
  have hz : cgCanonicalError base g (k+1)=0 := by
    simp only [cgCanonicalError,(cg_stopping_iff base hb g (k+1)).mpr hstop,map_zero]
  have hrec := cgCanonicalError_succ base hb g k
  have hs : canonicalCGStep base g k= -cgCanonicalError base g k := by
    calc
      _=(cgCanonicalError base g k+canonicalCGStep base g k)-cgCanonicalError base g k := by abel
      _= -cgCanonicalError base g k := by rw [← hrec,hz,zero_sub]
  rw [cgEnergy_sqrt base hb,hs,norm_neg]

/-- The undamped original deferred tail at a full actual cycle is precisely
the true FC remaining-error norm at that increment.
Use: the sharp damping-one comparison is the actual source FC coefficient.
Article: main_krylov, thm:DC, FC is epsilonHat=one.
Proof: the true deferred tail is the complete later actual CG step sum;
genuine terminal error telescoping gives minus the original remaining error. -/
theorem deferred_full_undamped_norm (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k l : ℕ) (hl : l<k)
    (hstop : referenceAtomCount base hb g≤k+1) :
    ‖deferredTail base g k 1 l‖=‖cgCanonicalError base g (l+1)‖ := by
  have hs : deferredTail base g k 1 l=∑ j∈Ico (l+1) (k+1),canonicalCGStep base g j := by
    rw [deferredTail,one_smul,Finset.sum_Ico_succ_top (by omega : l+1≤k)]
  have hz : cgCanonicalError base g (k+1)=0 := by
    simp only [cgCanonicalError,(cg_stopping_iff base hb g (k+1)).mpr hstop,map_zero]
  rw [hs,canonicalCGStep_sum base hb g (by omega : l+1≤k+1),hz,zero_sub,norm_neg]

/-- The exact original matrix maximum has the literal printed last-error
profile, with genuinely attained symmetric physical increments.
Use: no abstract energy symbol remains to be identified with the source norm.
Article: main_krylov, thm:DC, printed sharp square-root error coefficient.
Proof: the proved actual sharp matrix maximum has true last CG energy;
genuine next-step exhaustion identifies it with the squared last error norm. -/
theorem deferred_full_response_sharp (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hstop : referenceAtomCount base hb g=k+1)
    (epsilon : ℝ) (omega : ℕ → ℝ) (homega : ∀ l<k,0≤omega l) :
    IsGreatest {z : ℝ | ∃ E : ℕ → Matrix (Fin n) (Fin n) ℝ,
      (∀ l,(E l).IsSymm) ∧ (∀ l<k,‖E l‖≤omega l) ∧ z=‖deferredResponse base g k epsilon E‖}
      (∑ l∈range k,omega l*Real.sqrt (‖cgCanonicalError base g k‖^2+
        epsilon^2*(‖cgCanonicalError base g (l+1)‖^2-‖cgCanonicalError base g k‖^2))) := by
  have henergy : cgEnergy base g k=‖cgCanonicalError base g k‖^2 := by
    have he := congrArg (fun x : ℝ => x^2) (last_energy_error_norm base hb g k hstop.le)
    rw [Real.sq_sqrt (by rw [cgEnergy_eq_norm_sq base hb];exact sq_nonneg _)] at he
    exact he
  simpa only [henergy] using deferred_response_sharp base hb g k hstop.ge epsilon omega homega

/-- Nonamplifying original deferred estimates never exceed the literal actual
FC sharp coefficient on a full true cycle.
Use: the native arithmetic observed damping bound supplies the real hypothesis.
Article: main_krylov, thm:DC, sharp source comparison with FC.
Proof: the genuine deferred norm comparison bounds every real budget term;
true terminal tail telescoping identifies its damping-one coefficient with FC. -/
theorem deferred_full_coefficient_le_FC (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hstop : referenceAtomCount base hb g=k+1)
    (epsilon : ℝ) (habs : |epsilon|≤1) (omega : ℕ → ℝ) (homega : ∀ l<k,0≤omega l) :
    (∑ l∈range k,omega l*‖deferredTail base g k epsilon l‖)≤
      ∑ l∈range k,omega l*‖cgCanonicalError base g (l+1)‖ := by
  have hc := deferred_coefficient_le_FC base hb g k hstop.ge epsilon habs omega homega
  have he : (∑ l∈range k,omega l*‖deferredTail base g k 1 l‖)=
      ∑ l∈range k,omega l*‖cgCanonicalError base g (l+1)‖ :=
    sum_congr rfl (fun l hl => congrArg (fun t => omega l*t) (deferred_full_undamped_norm base hb g k l (mem_range.mp hl) hstop.le))
  exact he ▸ hc

/-- A positive real intermediate budget gives the original literal strict
FC sharp-coefficient improvement for every damping value below one in norm.
Use: the final-only and two-dimensional equality cases remain explicit.
Article: main_krylov, thm:DC, printed strict FC improvement.
Proof: use the proved real strict weighted-tail comparison and genuine full
CG terminal telescoping, preserving the source's exact strictness condition. -/
theorem deferred_full_coefficient_strict_FC (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hstop : referenceAtomCount base hb g=k+1)
    (epsilon : ℝ) (habs : |epsilon|<1) (omega : ℕ → ℝ) (homega : ∀ l<k,0≤omega l)
    (hpositive : ∃ l,l+1<k ∧ 0<omega l) :
    (∑ l∈range k,omega l*‖deferredTail base g k epsilon l‖)<
      ∑ l∈range k,omega l*‖cgCanonicalError base g (l+1)‖ := by
  have hc := deferred_coefficient_strict_FC base hb g k hstop.ge epsilon habs omega homega hpositive
  have he : (∑ l∈range k,omega l*‖deferredTail base g k 1 l‖)=
      ∑ l∈range k,omega l*‖cgCanonicalError base g (l+1)‖ :=
    sum_congr rfl (fun l hl => congrArg (fun t => omega l*t) (deferred_full_undamped_norm base hb g k l (mem_range.mp hl) hstop.le))
  exact he ▸ hc

end
end krylov.Cancellation
