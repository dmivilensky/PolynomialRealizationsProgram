import krylov.Methods.ProperKrylovMargins
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau and s8:dcsdef, true observed-pencil domains.
Use: derive both ordinary Schur inverse domains in any independent actual
observed basis lying in a proper reference Krylov flag.
Source: the proved strict proper-flag forms and genuine operator Gram calculus.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Both actual shifted Gram pencils are positive definite in every
independent retained basis of a genuine proper reference Krylov flag.
Use: smooth observed Schur rules need no assumed full physical spectral margin
and no assumed inverse model; the actual pre-exhaustion geometry supplies them.
Article: main_krylov, thm:radau and s8:dcsdef.
Proof: a nonzero real coefficient vector gives a nonzero genuine flag vector;
the strict proper-flag inequalities are exactly its two shifted Gram forms. -/
theorem proper_directionFlag_gram_shifts (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i<k+1,CG.gradient Q g i≠0) (mu upper : ℝ)
    (hlo : ∀ v : E,mu*‖v‖^2≤ inner ℝ v (Q v))
    (hhi : ∀ v : E,inner ℝ v (Q v)≤upper*‖v‖^2)
    (s : Fin p → E) (hs : LinearIndependent ℝ s) (hflag : ∀ i,s i∈directionFlag Q g k) :
    (crossGram (fun i => Q (s i)) s-mu • crossGram s s).PosDef ∧
      (upper • crossGram s s-crossGram (fun i => Q (s i)) s).PosDef := by
  let T := crossGram (fun i => Q (s i)) s
  let G := crossGram s s
  have ht : T.IsHermitian := (operatorGram_posDef Q hQ hpos hs).1
  have hg : G.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [G,crossGram,star_trivial]
    exact real_inner_comm _ _
  have hforms (c : Fin p → ℝ) (hc : c≠0) :
      mu*(c ⬝ᵥ (G*ᵥ c))<c ⬝ᵥ (T*ᵥ c) ∧
        c ⬝ᵥ (T*ᵥ c)<upper*(c ⬝ᵥ (G*ᵥ c)) := by
    have hv : combine s c≠0 := by
      intro he
      exact hc (funext (Fintype.linearIndependent_iff.mp hs c he))
    have hm : combine s c∈directionFlag Q g k :=
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hflag i))
    have hb := proper_directionFlag_strict_bounds Q hQ hpos g k hpre mu upper hlo hhi hm hv
    have hT : c ⬝ᵥ (T*ᵥ c)=inner ℝ (combine s c) (Q (combine s c)) :=
      (operatorGram_form Q s c).trans (real_inner_comm _ _)
    have hG : c ⬝ᵥ (G*ᵥ c)=‖combine s c‖^2 := by
      simpa only [ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq] using
        operatorGram_form (ContinuousLinearMap.id ℝ E) s c
    rw [hT,hG]
    exact hb
  constructor
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos (ht.sub (hg.smul (show IsSelfAdjoint mu from rfl)))
    intro c hc
    simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul]
    exact sub_pos.mpr (hforms c hc).1
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos ((hg.smul (show IsSelfAdjoint upper from rfl)).sub ht)
    intro c hc
    simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,dotProduct_sub,dotProduct_smul,smul_eq_mul]
    exact sub_pos.mpr (hforms c hc).2

end
end krylov.Methods
