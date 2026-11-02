import krylov.Convergence.WindowAugmentation
import krylov.LinearAlgebra.LeastGain
import krylov.Correction.SharpRestartEnergy
import krylov.Nonlinear.CoordinateLipschitz

/-!
Article: main_krylov, thm:grow and cor:xrF, physical/canonical normalization.
Use: derive the canonical normalized-column gain from the original physical
unit-column independence. The exact scale is sigma_flat*sqrt(lambda_min /
lambda_max), and the derivative congruence has its genuine cubic metric loss.
Source: actual positive-root energy, finite diagonal rescaling and the
ordinary operator composition norm; no canonical independence is assumed.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.Reference krylov.Correction krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Normalizing a true linear image after first normalizing its original
nonzero physical vector gives exactly the same actual canonical column. -/
theorem unitWindow_operator_unitWindow (J : E →L[ℝ] E) (s : Fin p → E)
    (hs : ∀ i,s i≠0) :
    unitWindow (fun i=>J (unitWindow s i))=unitWindow (fun i=>J (s i)) := by
  funext i
  simp only [unitWindow,rescaleWindow,map_smul,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),smul_smul]
  congr 1
  rw [_root_.mul_inv_rev]
  field_simp [norm_ne_zero_iff.mpr (hs i)]

/-- True norm bounds on a linear coordinate map transport actual normalized
column independence with only the sharp lower/upper metric ratio. -/
theorem unit_window_gain_linear (J : E →L[ℝ] E) (u : Fin p → E)
    (hu : ∀ i,‖u i‖=1) {a b σ : ℝ} (ha : 0<a) (hb : 0<b) (hσ : 0≤σ)
    (hlower : ∀ v,a*‖v‖≤‖J v‖) (hupper : ∀ v,‖J v‖≤b*‖v‖)
    (hgain : ∀ c : Fin p → ℝ,σ^2*‖WithLp.toLp 2 c‖^2≤‖combine u c‖^2)
    (c : Fin p → ℝ) :
    (a*σ/b)^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (fun i=>J (u i))) c‖^2 := by
  let d := fun i=>‖J (u i)‖
  let c' := fun i=>(d i)⁻¹*c i
  have hdpos (i : Fin p) : 0<d i := by
    have hh := hlower (u i)
    rw [hu i,mul_one] at hh
    exact ha.trans_le hh
  have hdle (i : Fin p) : d i≤b := by simpa only [hu i,mul_one] using hupper (u i)
  have hD : ‖(diagonal d:Matrix (Fin p) (Fin p) ℝ)‖≤b := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg hb.le).mpr
    intro i
    rw [Real.norm_of_nonneg (hdpos i).le]
    exact hdle i
  have hcoeff : ‖WithLp.toLp 2 c‖≤b*‖WithLp.toLp 2 c'‖ := by
    have he : WithLp.toLp 2 c=WithLp.toLp 2 ((diagonal d)*ᵥc') := by
      ext i
      simp only [Matrix.mulVec_diagonal,c']
      field_simp [(hdpos i).ne']
    rw [he]
    exact (Matrix.l2_opNorm_mulVec (diagonal d) (WithLp.toLp 2 c')).trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  have hcombine : combine (unitWindow (fun i=>J (u i))) c=J (combine u c') := by
    simp only [combine,unitWindow,rescaleWindow,map_sum,map_smul,c',d,smul_smul,mul_comm]
  have hphysical : σ*‖WithLp.toLp 2 c'‖≤‖combine u c'‖ := by
    apply (sq_le_sq₀ (mul_nonneg hσ (norm_nonneg _)) (norm_nonneg _)).mp
    simpa only [mul_pow] using hgain c'
  have hlow : a*σ*‖WithLp.toLp 2 c'‖≤‖combine (unitWindow (fun i=>J (u i))) c‖ := by
    rw [hcombine]
    simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hphysical ha.le).trans (hlower _)
  have hbound : (a*σ/b)*‖WithLp.toLp 2 c‖≤‖combine (unitWindow (fun i=>J (u i))) c‖ := by
    apply (mul_le_mul_of_nonneg_left hcoeff (show 0≤a*σ/b by positivity)).trans
    have he : (a*σ/b)*(b*‖WithLp.toLp 2 c'‖)=a*σ*‖WithLp.toLp 2 c'‖ := by field_simp
    rw [he]
    exact hlow
  simpa only [mul_pow] using (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hbound

/-- The original physical unit-column gain gives the actual canonical
unit-column gain; no independent canonical-window premise is introduced. -/
theorem raw_window_gain_linear (J : E →L[ℝ] E) (s : Fin p → E)
    (hs : ∀ i,s i≠0) {a b σ : ℝ} (ha : 0<a) (hb : 0<b) (hσ : 0≤σ)
    (hlower : ∀ v,a*‖v‖≤‖J v‖) (hupper : ∀ v,‖J v‖≤b*‖v‖)
    (hgain : ∀ c : Fin p → ℝ,σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow s) c‖^2)
    (c : Fin p → ℝ) :
    (a*σ/b)^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (fun i=>J (s i))) c‖^2 := by
  have hh := unit_window_gain_linear J (unitWindow s) (unitWindow_norm s hs) ha hb hσ hlower hupper hgain c
  rwa [unitWindow_operator_unitWindow J s hs] at hh

/-- The printed sigma_H is derived from true positive-root coordinates
and primitive physical spectral endpoints of Hstar. -/
theorem metric_window_gain {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (hs : ∀ i,s i≠0)
    {mu upper σ : ℝ} (hmu : 0<mu) (hu : 0<upper) (hσ : 0≤σ)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),mu*‖v‖^2≤ inner ℝ v (cgOperator H v))
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n),inner ℝ v (cgOperator H v)≤upper*‖v‖^2)
    (hgain : ∀ c : Fin p → ℝ,σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow s) c‖^2)
    (c : Fin p → ℝ) :
    (σ*Real.sqrt (mu/upper))^2*‖WithLp.toLp 2 c‖^2≤
      ‖combine (unitWindow (fun i=>cgOperator (metricRoot H) (s i))) c‖^2 := by
  let J := cgOperator (metricRoot H)
  have hlow (v : EuclideanSpace ℝ (Fin n)) : Real.sqrt mu*‖v‖≤‖J v‖ := by
    apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt hmu.le]
    simpa only [restart_root_pairing H hH,real_inner_self_eq_norm_sq] using hlower v
  have hhigh (v : EuclideanSpace ℝ (Fin n)) : ‖J v‖≤Real.sqrt upper*‖v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hu.le]
    simpa only [restart_root_pairing H hH,real_inner_self_eq_norm_sq] using hupper v
  have hh := raw_window_gain_linear J s hs (Real.sqrt_pos.mpr hmu) (Real.sqrt_pos.mpr hu) hσ hlow hhigh hgain c
  have he : Real.sqrt mu*σ/Real.sqrt upper=σ*Real.sqrt (mu/upper) := by
    rw [Real.sqrt_div hmu.le]
    ring
  simpa only [he] using hh

/-- A proved full synthesis gain gives the exact leastGain used by the
source convergence theorems, without losing an additive inverse constant. -/
theorem full_window_leastGain_of_gain {n : ℕ}
    (s : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1))) {σ : ℝ} (hσ : 0<σ)
    (hgain : ∀ c : Fin (n+1) → ℝ,σ^2*‖WithLp.toLp 2 c‖^2≤‖combine s c‖^2) :
    IsUnit (windowMatrix s).det ∧σ≤leastGain (windowMatrix s) := by
  let V := windowMatrix s
  have hV : IsUnit V.det := (full_window_inverse_of_gain s (sq_pos_of_pos hσ) hgain).1
  have hinv : ‖V⁻¹‖≤σ⁻¹ := by
    rw [←Matrix.l2_opNorm_toEuclideanCLM]
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hσ.le)
    intro x
    let c := V⁻¹*ᵥWithLp.ofLp x
    have he : combine s c=x := by
      rw [combine_windowMatrix]
      change WithLp.toLp 2 (V*ᵥ(V⁻¹*ᵥWithLp.ofLp x))=x
      rw [mulVec_mulVec,mul_nonsing_inv _ hV,one_mulVec,WithLp.toLp_ofLp]
    have hh := hgain c
    rw [he] at hh
    have hn : σ*‖WithLp.toLp 2 c‖≤‖x‖ :=
      (sq_le_sq₀ (mul_nonneg hσ.le (norm_nonneg _)) (norm_nonneg _)).mp (by simpa only [mul_pow] using hh)
    exact (le_inv_mul_iff₀ hσ).mpr hn
  have hnormpos : 0<‖V⁻¹‖ := norm_pos_iff.mpr (by
    intro hz
    have hh := nonsing_inv_mul V hV
    rw [hz,zero_mul] at hh
    have hc := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>M 0 0) hh
    norm_num at hc)
  refine ⟨hV,?_⟩
  change σ≤‖V⁻¹‖⁻¹
  exact (le_inv_comm₀ hσ hnormpos).mpr hinv

end
end krylov.Convergence
