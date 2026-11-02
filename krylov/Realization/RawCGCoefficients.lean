import krylov.Realization.RawCG
import krylov.Realization.RawFrozen

/-!
Article: main_krylov, prop:dict(i), actual measured frozen CG coefficients.
Use: identify the genuine supplied-matrix CG coefficients with the raw
leading determinant and adjacent-edge coefficients in the executed realization.
Source: proved actual Lanczos reconstruction, its determinant product,
terminal CG stopping and the genuine physical injected frozen recurrence.
-/

namespace krylov.Realization
noncomputable section
open Matrix Polynomial chebyshev1 krylov.Reference
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The genuine first-site CG line length equals the constructed leading determinant ratio.
Use: The genuine first-site CG line length equals the constructed leading determinant ratio.
Article: main_krylov, prop:dict(i).
Proof: Use consecutive actual Lanczos determinant products; cancel the nonzero positive leading product. -/
theorem raw_cg_length (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    CG.length (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) s=rawAlpha T s := by
  -- Consecutive true leading determinants recover the actual line length without a supplied recurrence.
  let Q := cgOperator T
  let g : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (JacobiData.site N 0)
  have hp := cgOperator_positive T hT
  have hpre (i : ℕ) (hi : i<N) : CG.gradient Q g i≠0 := raw_cg_nonstagnation T hT htri hneg i hi
  have hdet (m : ℕ) (hm : m≤N) : (rawBlock T 0 m (by omega)).det=
      ∏ i : Fin m, (CG.length Q g i.val)⁻¹ := by
    rw [← raw_lanczosMatrix_prefix T hT htri hneg m hm]
    exact CG.lanczosMatrix_det Q hp.1 hp.2 g m (fun i hi => hpre i (lt_of_lt_of_le hi hm))
  have hd0 := hdet s hs.le
  have hd1 := hdet (s+1) (by omega)
  rw [Fin.prod_univ_castSucc] at hd1
  simp only [Fin.val_castSucc,Fin.val_last] at hd1
  have hprod : (∏ i : Fin s, (CG.length Q g i.val)⁻¹)≠0 := by
    rw [← hd0]
    exact (rawBlock_posDef T hT 0 s (by omega)).det_pos.ne'
  symm
  rw [rawAlpha_det T hT htri hneg s hs,hd0,hd1]
  rw [div_mul_eq_div_div,div_self hprod,one_div,inv_inv]

/-- Each internal genuine CG recurrence ratio equals the raw adjacent-edge coefficient.
Use: Each internal genuine CG recurrence ratio equals the raw adjacent-edge coefficient.
Article: main_krylov, prop:dict(i).
Proof: The measured adjacent Lanczos entry and the true positive line length determine its square; actual CG beta is nonnegative. -/
theorem raw_cg_beta_internal (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s+1<N) :
    CG.beta (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) s=rawBeta T s := by
  -- The true measured adjacent entry fixes the nonnegative squared recurrence coefficient.
  let Q := cgOperator T
  let g : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (JacobiData.site N 0)
  let i : Fin N := ⟨s,by omega⟩
  let j : Fin N := ⟨s+1,hs⟩
  have hp := cgOperator_positive T hT
  have he := CG.lanczosMatrix_adjacent Q hp.1 hp.2 g N
    (fun i hi => raw_cg_nonstagnation T hT htri hneg i hi) i j rfl
  rw [raw_lanczosMatrix T hT htri hneg] at he
  change T i j= -Real.sqrt (CG.beta Q g s)/CG.length Q g s at he
  rw [raw_cg_length T hT htri hneg s (by omega)] at he
  have hprod := (eq_div_iff (rawAlpha_pos T hT htri hneg s (by omega)).ne').mp he
  have hβ : 0≤CG.beta Q g s := by unfold CG.beta; positivity
  rw [rawBeta_edge T i j rfl,hprod,neg_sq,Real.sq_sqrt hβ]

/-- Every used genuine CG recurrence ratio equals its raw coefficient, including the terminal zero ratio.
Use: Every used genuine CG recurrence ratio equals its raw coefficient, including the terminal zero ratio.
Article: main_krylov, prop:dict(i).
Proof: Internal edges use the measured identity; the last true gradient vanishes at the full actual active dimension. -/
theorem raw_cg_beta (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (s : ℕ) (hs : s<N) :
    CG.beta (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) s=rawBeta T s := by
  by_cases hlast : s+1<N
  · exact raw_cg_beta_internal T hT htri hneg s hlast
  · have he : s+1=N := by omega
    have hzero : CG.gradient (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) (s+1)=0 := by
      rw [he]
      simpa only [raw_referenceAtomCount T hT htri hneg] using cg_terminates T hT (WithLp.toLp 2 (JacobiData.site N 0))
    rw [CG.beta,hzero,norm_zero,zero_pow (by decide : 2≠0),zero_div]
    simp [rawBeta,rawJacobi,he]

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The actual physical two-memory executor uses the coefficients measured by the genuine supplied-matrix CG run.
Use: The actual physical two-memory executor uses the coefficients measured by the genuine supplied-matrix CG run.
Article: main_krylov, prop:dict(i).
Proof: Substitute the proved actual alpha and beta identities into the genuine physical injected recurrence. -/
theorem raw_injected_frozen_measured (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0)
    (Q : E →ₗ[ℝ] E) (input : ℕ → E) (initial : E) (s : ℕ) (hs : s+1<N) :
    let v := injectedFixedRun ((rawJacobi T).realization dictionaryInterval) Q input initial
    let Q₀ := cgOperator T
    let g₀ : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (JacobiData.site N 0)
    v (s+2) 0=v (s+1) 0-CG.length Q₀ g₀ (s+1) • (Q (v (s+1) 0)+input (s+1))+
      (CG.length Q₀ g₀ (s+1)*CG.beta Q₀ g₀ s/CG.length Q₀ g₀ s) • (v (s+1) 0-v s 0) := by
  have h := raw_injected_frozen T hT htri hneg Q input initial s hs
  dsimp only at h ⊢
  rw [rawMomentum,ite_eq_right (Nat.succ_ne_zero s),Nat.add_sub_cancel] at h
  rw [← raw_cg_length T hT htri hneg (s+1) hs,← raw_cg_length T hT htri hneg s (by omega),
    ← raw_cg_beta T hT htri hneg s (by omega)] at h
  exact h

/-- The actual initial physical injected update uses the genuine supplied-matrix CG line length.
Use: The actual initial physical injected update uses the genuine supplied-matrix CG line length.
Article: main_krylov, prop:dict(i).
Proof: Identify the actual first executor update and substitute the proved true CG length. -/
theorem raw_injected_frozen_measured_zero (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i j : Fin N, i.val+1 < j.val ∨ j.val+1 < i.val → T i j=0)
    (hneg : ∀ i j : Fin N, i.val+1=j.val → T i j < 0) (hN : 0 < N)
    (Q : E →ₗ[ℝ] E) (input : ℕ → E) (initial : E) :
    injectedFixedRun ((rawJacobi T).realization dictionaryInterval) Q input initial 1 0=
      initial-CG.length (cgOperator T) (WithLp.toLp 2 (JacobiData.site N 0)) 0 • (Q initial+input 0) := by
  have h := twoTerm_injected_zero ((rawJacobi T).method dictionaryInterval) Q input initial
  rw [raw_method_gamma,← raw_cg_length T hT htri hneg 0 hN] at h
  exact h

end
end krylov.Realization
