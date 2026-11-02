import krylov.Correction.ObservedGateAcceptance
import krylov.Correction.GatedExecution
import krylov.Stability.ObservedProjection

/-!
Article: main_krylov, thm:UCq and thm:UCg, genuine accepted correction domains.
Use: Derive the real accepted gated phase and its model/Gram spectral bounds
from the actual measured-data margins before the finite residual induction.
Source: proved quantitative observed gates, the genuine RFC phase executor,
true spectral norm calculus and Rayleigh form perturbation.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.LinearAlgebra krylov.Stability chebyshev1
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Both actual observed tests pass under the true quantitative pair and Gram margins, and the real phase is exactly its original one-model correction.
Use: Justify the genuine accepted model correction and all true normalized spectral domains in the uniform cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, actual accepted phase.
Proof: Derive the genuine spectral decision and the true old-window defect decision from actual relative observations. Executing those proved accepted branches returns the real coefficient-model movement and its actual correction-oracle gradient.
-/
theorem gatedArrayPhase_accepted {p : ℕ} (S Y : Fin p → E) (g d z : E)
    (B : E →L[ℝ] E) {γ η δ : ℝ} (hp : 0<p) (hγ : 0≤γ) (hη : 0≤η) (hhalf : η≤1/2)
    (hs : ∀ i : Fin (p+1), (Fin.cons d S : Fin (p+1) → E) i≠0)
    (hy : ∀ i : Fin (p+1), ‖(Fin.cons z Y : Fin (p+1) → E) i-(Fin.cons d S : Fin (p+1) → E) i‖≤
      η*‖(Fin.cons d S : Fin (p+1) → E) i‖)
    (hG : ‖crossGram (unitWindow (Fin.cons d S)) (unitWindow (Fin.cons d S))-1‖≤δ)
    (hmargin : δ+((p+1 : ℕ) : ℝ)*η+γ*η≤1-γ) (hdefect : (p : ℝ)*(4*η)<1) :
    let U : Fin (p+1) → E := Fin.cons d S
    let Z : Fin (p+1) → E := Fin.cons z Y
    let χ := combine U (modelCoefficients U (pairModel U Z) (searchedGradient g d z))
    (gatedArrayPhase γ S Y g d z B).movement=χ ∧
      (gatedArrayPhase γ S Y g d z B).gradient=searchedGradient g d z+B χ := by
  have hη1 : η<1 := by linarith
  have hgate := pair_spectralGate_of_gram (Fin.cons d S) (Fin.cons z Y) hs hγ hη hη1 hy hG hmargin
  have hs' (i : Fin p) : S i≠0 := by simpa only [Fin.cons_succ] using hs i.succ
  have hy' (i : Fin p) : ‖Y i-S i‖≤η*‖S i‖ := by simpa only [Fin.cons_succ] using hy i.succ
  have hgate' : 0<p ∧ ‖pairDefect S Y‖<1 :=
    ⟨hp,(relative_pairDefect_norm_bound S Y hs' hη hhalf hy').trans_lt hdefect⟩
  unfold gatedArrayPhase
  rw [ite_eq_left hgate,rfcArrayPhase,ite_eq_left hgate']
  exact ⟨add_zero _,rfl⟩

/-- Every actual Hermitian eigenvalue is bounded in absolute value by the genuine spectral matrix norm.
Use: Justify the genuine accepted model correction and all true normalized spectral domains in the uniform cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, actual accepted phase.
Proof: Reuse the proved polynomial spectral norm identity for the identity polynomial and bound the true finite eigenvalue coordinate by its supremum norm.
-/
theorem eigenvalue_abs_le_spectral_norm {p : ℕ} (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian)
    (i : Fin p) : |hH.eigenvalues i|≤‖H‖ := by
  have hn := opNorm_aeval_eq (Polynomial.X : Polynomial ℝ) H hH
  simp only [Polynomial.aeval_X,Polynomial.eval_X,opNorm] at hn
  rw [hn]
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm hH.eigenvalues i

/-- Every genuine Hermitian matrix within one half of the identity has all true eigenvalues between one half and four, including empty coefficient spaces.
Use: Justify the genuine accepted model correction and all true normalized spectral domains in the uniform cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, actual accepted phase.
Proof: Rayleigh norm perturbation gives the lower endpoint. The genuine matrix/identity triangle estimate bounds its spectral norm, which bounds each actual eigenvalue.
-/
theorem near_identity_spectral_bounds {p : ℕ} (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.IsHermitian)
    (hnear : ‖H-1‖≤(1/2 : ℝ)) :
    ∀ i, (1/2 : ℝ)≤hH.eigenvalues i ∧ hH.eigenvalues i≤4 := by
  have hbase : ∀ i, (1 : ℝ)≤(Matrix.isHermitian_one : (1 : Matrix (Fin p) (Fin p) ℝ).IsHermitian).eigenvalues i := by
    apply spectral_lower_of_form
    intro v
    simp only [one_mul,map_one,one_apply_eq_self,real_inner_self_eq_norm_sq,le_refl]
  have hlo := spectral_lower_perturbation 1 H Matrix.isHermitian_one hH hbase hnear
  have hi : ‖(1 : Matrix (Fin p) (Fin p) ℝ)‖≤1 := by
    rw [Matrix.cstar_norm_def,map_one]
    exact ContinuousLinearMap.norm_id_le
  have hnorm : ‖H‖≤4 := by
    have ht := norm_le_norm_sub_add H (1 : Matrix (Fin p) (Fin p) ℝ)
    linarith
  intro i
  exact ⟨by have h := hlo i; norm_num at h; exact h,
    (le_abs_self _).trans ((eigenvalue_abs_le_spectral_norm H hH i).trans hnorm)⟩

end
end krylov.Correction
