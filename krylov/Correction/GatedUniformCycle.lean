import krylov.Correction.GatedSmallCutoff
import krylov.Correction.GatedHistoryTerminal

/-!
Article: main_krylov, thm:UCg(i,ii), genuine whole spectral-class cycle bounds.
Use: Prove the actual quadratic terminal metric-gradient bound and the refined
performed-last-correction bound with one constant and radius before every
positive reference of the prescribed spectral conditioning and every real run.
Source: original actual gated executor, constructed uniform cutoff prefixes,
true scale-uniform small-line geometry, actual gradient propagation and genuine
full observed terminal correction reconstruction. The actual initial metric
gradient is bounded by one; exact data homogeneity removes that normalization.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

set_option maxHeartbeats 800000 in
/-- Every genuine defined full-memory gated-RFC cycle has the original whole spectral-class quadratic terminal bound and performed-last-correction refinement for positive perturbation budgets and bounded actual initial metric gradient, with constants chosen before every reference, spectral scale and real operator run.
Use: Supply the full original uniform cycle argument before the zero-budget and exact initial-gradient scaling corollaries.
Article: main_krylov, thm:UCg(i,ii), genuine whole spectral-class cycle bounds.
Proof: Choose the actual common cutoff allowances and recording radius before the reference. At the first small preterminal line, the true recorded-prefix residual and positive reference coercivity make the actual gradient quadratic; genuine finite growth propagates it, and an actual last query gives one further measured-model contraction. If no such line occurs, the real full last prefix passes both gates and has the proved refined terminal residual. The actual last line is never divided by; the true smallest and largest reference bounds enter only through their condition-number ratio.
-/
theorem gated_uniform_cycle_normalized (n : ℕ) (hn : 2≤n) (κ γ : ℝ)
    (hκ : 1≤κ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i) → ‖cgOperator base‖≤κ*μ →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0<ε → ε<ε₀ → gatedFullRunDefined γ A B g n →
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g‖≤1 →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
      let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      ‖J (probedGradient m A B g n)‖≤C*ε^2 ∧
        ((probedPhase m A B g (n-1)).trace≠[] →
          ‖J (probedGradient m A B g n)‖≤C*(ε^2*‖J (probedGradient m A B g (n-1))‖+ε^3)) := by
  have hn1 : 1≤n := by omega
  have hκ0 : 0≤κ := le_trans (by norm_num) hκ
  obtain ⟨a,Cs,M,δ,ha,ha1,hCs,hM,hδ,hangle,hprefixes⟩ := gated_uniform_cutoff_prefix n hn1 γ hγ hγ1
  obtain ⟨ρ,hρ,hrecording⟩ := gated_recording_radius n γ hγ
  let K := 2*gatedCorrectionConstant n γ
  let L := (gatedGrowthConstant n γ)^n
  let D := 8*κ*M+20*κ*Cs
  let P := L*D
  let A₀ := 4*(n : ℝ)*(2+K)*Cs
  let B₀ := 8*(n : ℝ)*Real.sqrt n*(2+K)^2
  let Q := 1+A₀+B₀
  let Λ := (5*((Real.sqrt (γ/4))⁻¹*(n : ℝ)*(γ/2)⁻¹*Real.sqrt n))*(2+K)
  let C := 1+P+Q*(1+L)+Λ*P
  have hK : 0≤K := mul_nonneg (by norm_num) (gatedCorrectionConstant_nonneg n γ)
  have hcgrow : 1≤gatedGrowthConstant n γ := by
    unfold gatedGrowthConstant
    have ht : 0≤10*(n : ℝ)/γ := by positivity
    linarith
  have hcgrow0 := (by norm_num : (0 : ℝ)≤1).trans hcgrow
  have hL : 0≤L := pow_nonneg hcgrow0 n
  have hD : 0≤D := by dsimp only [D]; positivity
  have hP : 0≤P := mul_nonneg hL hD
  have hA₀ : 0≤A₀ := by dsimp only [A₀]; positivity
  have hB₀ : 0≤B₀ := by dsimp only [B₀]; positivity
  have hQ : 0<Q := by dsimp only [Q]; linarith
  have hΛ : 0≤Λ := by dsimp only [Λ]; positivity
  have hQL : 0≤Q*(1+L) := mul_nonneg hQ.le (by linarith)
  have hΛP : 0≤Λ*P := mul_nonneg hΛ hP
  have hC : 0<C := by dsimp only [C]; linarith
  have hPC : P≤C := by dsimp only [C]; linarith
  have hQLC : Q*(1+L)≤C := by dsimp only [C]; linarith
  have hΛPC : Λ*P≤C := by dsimp only [C]; linarith
  have hQC : Q≤C := by nlinarith [mul_nonneg hQ.le hL]
  have hA₀Q : A₀≤Q := by dsimp only [Q]; linarith
  have hB₀Q : B₀≤Q := by dsimp only [Q]; linarith
  refine ⟨min 1 (min δ ρ),C,lt_min zero_lt_one (lt_min hδ hρ),hC,?_⟩
  intro base hb μ hμ hspec hnorm A B g ε hε he hdefined hinit hA hB
  let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let W := fun i => selectedWindow fullMemory (methodRun m A B g i)
  let G := fun i => J (probedGradient m A B g i)
  let η := (1+K)*ε
  have hη : 0≤η := by dsimp only [η]; positivity
  have hεη : ε≤η := by dsimp only [η]; nlinarith
  have hε1 : ε≤1 := he.le.trans (min_le_left _ _)
  have heδ : ε<δ := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heρ : ε≤ρ := he.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hr := hrecording ε hε.le heρ
  have hcut := hprefixes n base hb A B g ε hε heδ hdefined hinit hA hB
  have hrecord := gated_uniform_recorded_bounds base hb fullMemory γ hγ A B g n hε.le hA hB hr.1 hr.2.1 hr.2.2
  have hnext i (hi : i<n) : ‖G (i+1)‖≤gatedGrowthConstant n γ*‖G i‖ := hcut.2.1 i hi
  have hbound i (hi : i≤n) : ‖G i‖≤L := by
    have ht := finite_norm_growth_between G hcgrow0 n hnext 0 i (Nat.zero_le i) hi
    rw [Nat.sub_zero] at ht
    have hp := mul_le_mul (pow_le_pow_right₀ hcgrow hi) hinit (norm_nonneg (G 0)) (pow_nonneg hcgrow0 n)
    exact ht.trans (hp.trans_eq (by rw [mul_one]))
  have hlen i : (W i).length=i := by dsimp only [W]; rw [fullWindow_methodRun,executedPairs_length]
  have hy i (hi : i<n) : ∀ j : Fin (W i).length,
      ‖dualWindow base (windowImages (W i)) j-primalWindow base (windowSteps (W i)) j‖≤
        η*‖primalWindow base (windowSteps (W i)) j‖ :=
    selectedWindow_pair_bound fullMemory m A B g i R J η (fun j hj => hrecord.2 j (hj.trans hi))
  have hlast : (n-1)+1=n := by omega
  have hlastN : n-1<n := by omega
  have hdim : (W (n-1)).length+1=n := by rw [hlen]; omega
  have hε3 : ε^3≤ε^2 := by nlinarith [mul_le_mul_of_nonneg_right hε1 (sq_nonneg ε)]
  dsimp only
  by_cases hex : ∃ j : ℕ, j<n-1 ∧ ‖R (gatedObservedLineStep γ A B g j)‖<M*ε^2
  · let j := Nat.find hex
    have hj := Nat.find_spec hex
    change j<n-1 ∧ ‖R (gatedObservedLineStep γ A B g j)‖<M*ε^2 at hj
    have hjN : j<n := by omega
    have hbefore : ∀ l<j, M*ε^2≤‖R (gatedObservedLineStep γ A B g l)‖ := by
      intro l hl
      by_contra hs
      have hjle := Nat.find_min' hex (show l<n-1 ∧ ‖R (gatedObservedLineStep γ A B g l)‖<M*ε^2 from ⟨by omega,lt_of_not_ge hs⟩)
      change j≤l at hjle
      omega
    have hpre := hcut.2.2 j hjN.le hbefore
    have hsmall : ‖G j‖≤D*ε^2 := observed_prefix_small_line_gradient_bound base hb (W j)
      (probedGradient m A B g j) (A j) n hn1 (by rw [hlen]; omega) hμ hκ0 hγ.le ha.le hη hεη
      hspec hnorm (hdefined j hjN).1 (hdefined j hjN).2 hpre (hy j hjN) (hA j hjN) hangle hcut.1 hj.2.le
    have hlate i (hji : j≤ i) (hi : i≤n) : ‖G i‖≤P*ε^2 := by
      have ht := finite_norm_growth_between G hcgrow0 n hnext j i hji hi
      have hp := mul_le_mul (pow_le_pow_right₀ hcgrow (show i-j≤n by omega)) hsmall
        (norm_nonneg (G j)) (pow_nonneg hcgrow0 n)
      exact ht.trans (hp.trans_eq (by dsimp only [P,L]; ring))
    refine ⟨(hlate n (by omega) le_rfl).trans (mul_le_mul_of_nonneg_right hPC (sq_nonneg ε)),?_⟩
    intro htrace
    have ht := gated_history_full_correction_contraction base hb (methodRun m A B g (n-1))
      (A (n-1)) (B (n-1)) hdim hγ hε.le hη hεη hr.1 hr.2.1 (hy (n-1) hlastN)
      (hA (n-1) hlastN) (hB (n-1) hlastN) htrace
    change ‖G ((n-1)+1)‖≤(5*((Real.sqrt (γ/4))⁻¹*(n : ℝ)*(γ/2)⁻¹*Real.sqrt n))*(ε+η)*‖G (n-1)‖ at ht
    rw [hlast,show ε+η=(2+K)*ε by dsimp only [η]; ring] at ht
    have ht' : ‖G n‖≤Λ*ε*‖G (n-1)‖ := ht.trans_eq (by dsimp only [Λ]; ring)
    have hout : ‖G n‖≤(Λ*P)*ε^3 :=
      (ht'.trans (mul_le_mul_of_nonneg_left (hlate (n-1) (by omega) hlastN.le) (by positivity))).trans_eq (by ring)
    apply (hout.trans (mul_le_mul_of_nonneg_right hΛPC (pow_nonneg hε.le 3))).trans
    apply mul_le_mul_of_nonneg_left ?_ hC.le
    nlinarith [mul_nonneg (sq_nonneg ε) (norm_nonneg (G (n-1)))]
  · have hbefore : ∀ j<n-1, M*ε^2≤‖R (gatedObservedLineStep γ A B g j)‖ := by
      intro j hj
      by_contra hs
      exact hex ⟨j,hj,lt_of_not_ge hs⟩
    have hpre := hcut.2.2 (n-1) hlastN.le hbefore
    have ht := gated_history_full_prefix_bound base hb (methodRun m A B g (n-1)) (A (n-1)) (B (n-1))
      hn hdim hγ.le hγ1 ha.le hε.le hK (hdefined (n-1) hlastN).1 (hdefined (n-1) hlastN).2 hpre
      (hA (n-1) hlastN) (hB (n-1) hlastN) (hy (n-1) hlastN) hangle hcut.1
    have hout := ht.2
    change ‖G ((n-1)+1)‖≤4*(n : ℝ)*(2+K)*ε*(Cs*ε^2+
      Real.sqrt n*(((2+K)*ε)*‖R (gatedObservedLineStep γ A B g (n-1))‖)) at hout
    rw [hlast] at hout
    have hline := actual_line_norm_bound (canonicalOperator base (A (n-1))) (G (n-1))
      (R (m.direction (methodRun m A B g (n-1)))) (hA (n-1) hlastN) (hεη.trans hr.1)
    rw [canonicalOperator_primal base hb,canonical_lineLength base hb] at hline
    have hline' : ‖R (gatedObservedLineStep γ A B g (n-1))‖≤2*‖G (n-1)‖ := by
      unfold gatedObservedLineStep
      rw [map_smul]
      exact hline
    have hcoarse : ‖G n‖≤A₀*ε^3+B₀*(ε^2*‖G (n-1)‖) := by
      have hb' := hout.trans (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (Cs*ε^2))
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hline' (by positivity : 0≤(2+K)*ε)) (Real.sqrt_nonneg n))) (by positivity))
      exact hb'.trans_eq (by dsimp only [A₀,B₀]; ring)
    have hrefined : ‖G n‖≤Q*(ε^2*‖G (n-1)‖+ε^3) := by
      have hb' := hcoarse.trans (add_le_add
        (mul_le_mul_of_nonneg_right hA₀Q (pow_nonneg hε.le 3))
        (mul_le_mul_of_nonneg_right hB₀Q (mul_nonneg (sq_nonneg ε) (norm_nonneg _))))
      exact hb'.trans_eq (by ring)
    refine ⟨?_,fun _ => hrefined.trans (mul_le_mul_of_nonneg_right hQC (by positivity))⟩
    have hb' := hrefined.trans (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left (hbound (n-1) hlastN.le) (sq_nonneg ε)) hε3) hQ.le)
    have hb'' : ‖G n‖≤(Q*(1+L))*ε^2 := hb'.trans_eq (by ring)
    exact hb''.trans (mul_le_mul_of_nonneg_right hQLC (sq_nonneg ε))

end
end krylov.Correction
