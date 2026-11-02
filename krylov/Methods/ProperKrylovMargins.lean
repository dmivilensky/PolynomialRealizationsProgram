import krylov.Reference.LanczosStrictWindow
import krylov.Methods.CGFlags
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau and s8:dcsdef, actual proper-Krylov margins.
Use: derive strictly positive shifted observed models before true exhaustion,
even when the physical operator itself reaches a class spectral endpoint.
Source: the proved strict Ritz theorem and actual residual/direction Krylov spans.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every vector in the true old CG flag is synthesized by the actual
normalized residuals in that same proper prefix.
Use: transport genuine strict Ritz margins to arbitrary observed bases.
Article: main_krylov, thm:radau.
Proof: reuse the actual polynomial Krylov span dictionaries, then rescale
each genuine residual generator by its true norm. -/
theorem directionFlag_residual_synthesis (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i<k,CG.gradient Q g i≠0) {v : E} (hv : v∈directionFlag Q g k) :
    ∃ c : Fin k → ℝ,(∑ i : Fin k,c i • CG.residualUnit Q g i.val)=v := by
  have hl (i : ℕ) (hi : i<k) : CG.length Q g i≠0 :=
    (CG.invariant_line_pos Q hpos g i (CG.invariant Q hQ hpos g i
      (fun j hj => hpre j (hj.trans hi))) (hpre i hi)).2.1.ne'
  have hflag : directionFlag Q g k=Submodule.span ℝ (CG.gradient Q g '' Set.Iio k) :=
    (CG.krylovSpace_eq_span_directions Q g k hl).symm.trans (CG.krylovSpace_eq_span_gradients Q g k hl)
  have hle : directionFlag Q g k≤Submodule.span ℝ (Set.range (fun i : Fin k => CG.residualUnit Q g i.val)) := by
    rw [hflag]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    have he : CG.gradient Q g i=‖CG.gradient Q g i‖ • CG.residualUnit Q g i :=
      (NormedSpace.norm_smul_normalize _).symm
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩)
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hle hv)

/-- True physical spectral bounds become strict on every genuine proper
CG flag, including class-endpoint matrices.
Use: actual arithmetic/harmonic Schur rules have ordinary inverse domains
before the active cycle is exhausted; full physical strict margins are unneeded.
Article: main_krylov, thm:radau and s8:dcsdef.
Proof: the one-more-active-residual Ritz theorem gives both strictly positive
Lanczos shifts. Synthesize the actual flag vector in the proved orthonormal
residual prefix and transfer its true quadratic form and norm. -/
theorem proper_directionFlag_strict_bounds (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i<k+1,CG.gradient Q g i≠0) (mu upper : ℝ)
    (hlo : ∀ v : E,mu*‖v‖^2≤ inner ℝ v (Q v))
    (hhi : ∀ v : E,inner ℝ v (Q v)≤upper*‖v‖^2)
    {v : E} (hv : v∈directionFlag Q g k) (hv0 : v≠0) :
    mu*‖v‖^2< inner ℝ v (Q v) ∧ inner ℝ v (Q v)<upper*‖v‖^2 := by
  have hp : ∀ i<k,CG.gradient Q g i≠0 := fun i hi => hpre i (by omega)
  obtain ⟨c,hc⟩ := directionFlag_residual_synthesis Q hQ hpos g k hp hv
  have hc0 : c≠0 := by
    intro he
    rw [he] at hc
    simp only [Pi.zero_apply,zero_smul,Finset.sum_const_zero] at hc
    exact hv0 hc.symm
  have hT := CG.lanczosMatrix_posDef Q hQ hpos g k hp
  have hr := CG.lanczosMatrix_strict_window Q hQ hpos g k hpre mu upper hlo hhi
  have hL := (positive_lower_shift_iff _ hT.1 mu).mpr (fun i => (hr i).1)
  have hH := (positive_upper_shift_iff _ hT.1 upper).mpr (fun i => (hr i).2)
  have hl := hL.dotProduct_mulVec_pos hc0
  have hh := hH.dotProduct_mulVec_pos hc0
  have hn := CG.lanczosResidualSynthesis_norm_sq Q hQ hpos g k hp c
  rw [hc] at hn
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_sub,dotProduct_smul,smul_eq_mul] at hl hh
  have hsum : c ⬝ᵥ c=‖v‖^2 := by
    rw [hn]
    simp only [dotProduct,pow_two]
  have hform : c ⬝ᵥ (CG.lanczosMatrix Q g k*ᵥ c)=inner ℝ v (Q v) := by
    simpa only [star_trivial,hc] using CG.lanczosMatrix_form Q g k c
  rw [hsum,hform] at hl hh
  exact ⟨by linarith,by linarith⟩

end
end krylov.Methods
