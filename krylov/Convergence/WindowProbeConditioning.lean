import krylov.Convergence.WindowAugmentation
import krylov.Convergence.SecantWindowGates

/-!
Article: main_krylov, thm:Ip, actual RFC augmented-frame conditioning.
Use: derive a full genuine probe-frame inverse bound from the article's
independence of only the stored steps. Source: actual convergent secant
queries, measured direction conjugacy, and the proved sharp Gram block
bound σ²−√p ε. No independence of the full augmented frame is assumed.
-/

namespace krylov.Convergence
noncomputable section
open Set Filter Topology Matrix krylov.Methods
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {p : ℕ} {α : Type*} {l : Filter α}

theorem unitWindow_snoc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Fin p → E) (d : E) :
    unitWindow (Fin.snoc s d)=Fin.snoc (unitWindow s) (‖d‖⁻¹ • d) := by
  funext i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [unitWindow,rescaleWindow,Fin.snoc_last]
  · simp only [unitWindow,rescaleWindow,Fin.snoc_castSucc]

/-- Every late actual probe frame is genuinely nonsingular with a uniform
inverse bound derived from the original stored-window gain. -/
theorem source_probe_frame_conditioning
    (G : EuclideanSpace ℝ (Fin (p+1)) → EuclideanSpace ℝ (Fin (p+1)))
    (H : EuclideanSpace ℝ (Fin (p+1)) → EuclideanSpace ℝ (Fin (p+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (p+1)))
    (S : Set (EuclideanSpace ℝ (Fin (p+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (p+1)))∈S) {L : ℝ≥0} (hH : LipschitzOnWith L H S)
    (hH₀ : H 0=ContinuousLinearMap.id ℝ _) (hG : ∀ z∈S,HasFDerivAt G (H z) z)
    (a b : α → Fin p → EuclideanSpace ℝ (Fin (p+1)))
    (q : α → EuclideanSpace ℝ (Fin (p+1)))
    (ha : ∀ i,Tendsto (fun z=>a z i) l (𝓝 0))
    (hb : ∀ i,Tendsto (fun z=>b z i) l (𝓝 0))
    (hm : ∀ᶠ z in l,(∀ i,a z i∈S) ∧(∀ i,b z i∈S))
    (hne : ∀ᶠ z in l,(∀ i,b z i-a z i≠0) ∧q z≠0)
    (hconj : ∀ᶠ z in l,∀ i,inner ℝ (G (b z i)-G (a z i)) (q z)=0)
    {σ : ℝ} (hσ : 0<σ) (hσ₁ : σ≤1)
    (hgain : ∀ᶠ z in l,∀ c : Fin p → ℝ,
      σ^2*‖WithLp.toLp 2 c‖^2≤‖combine (unitWindow (fun i=>b z i-a z i)) c‖^2) :
    ∀ᶠ z in l,
      IsUnit (windowMatrix (unitWindow (Fin.snoc (fun i=>b z i-a z i) (q z)))).det ∧
      ‖(windowMatrix (unitWindow (Fin.snoc (fun i=>b z i-a z i) (q z))))⁻¹‖≤
        (σ^2/2)⁻¹+1 := by
  let ε := fun z=>(L:ℝ)/2*sourceWindowRadius (a z) (b z)
  have hε : Tendsto ε l (𝓝 0) := by
    have hh := tendsto_finsetSum Finset.univ (fun i _=>(ha i).norm.add (hb i).norm)
    have hr : Tendsto (fun z=>sourceWindowRadius (a z) (b z)) l (𝓝 0) := by
      simpa only [sourceWindowRadius,norm_zero,add_zero,Finset.sum_const_zero] using hh
    simpa only [mul_zero] using hr.const_mul ((L:ℝ)/2)
  have hsmall : ∀ᶠ z in l,Real.sqrt p*ε z≤σ^2/2 := by
    have hh : Tendsto (fun z=>Real.sqrt p*ε z) l (𝓝 0) := by
      simpa only [mul_zero] using hε.const_mul (Real.sqrt p)
    exact (hh.eventually (gt_mem_nhds (by positivity : (0:ℝ)<σ^2/2))).mono fun _ h=>h.le
  filter_upwards [hm,hne,hconj,hgain,hsmall] with z hz hn hc hg hs
  have he : 0≤ε z := mul_nonneg (by positivity) (sourceWindowRadius_nonneg _ _)
  have herr i : ‖G (b z i)-G (a z i)-(b z i-a z i)‖≤ε z*‖b z i-a z i‖ := by
    have hh := secant_image_endpoint_bound G H S hS h₀ hH hG _ _ (hz.1 i) (hz.2 i)
    rw [hH₀,ContinuousLinearMap.id_apply] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.single_le_sum (fun j _=>add_nonneg (norm_nonneg (a z j)) (norm_nonneg (b z j)))
      (Finset.mem_univ i)
  have horth i : |inner ℝ (unitWindow (fun i=>b z i-a z i) i) (‖q z‖⁻¹ • q z)|≤ε z :=
    observed_conjugacy_unit_pairing _ _ _ (hn.1 i) hn.2 (herr i) (hc i)
  have hqunit : ‖‖q z‖⁻¹ • q z‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn.2)]
  apply full_window_inverse_of_gain _ (by positivity : (0:ℝ)<σ^2/2)
  intro c
  rw [unitWindow_snoc]
  have hh := augmented_window_gain_sq _ _ hσ.le hσ₁ he hqunit hg horth c
  exact (mul_le_mul_of_nonneg_right (by linarith : σ^2/2≤σ^2-Real.sqrt p*ε z)
    (sq_nonneg _)).trans hh

end
end krylov.Convergence
