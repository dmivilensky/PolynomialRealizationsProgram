import krylov.Correction.RFCUniformPrefix
import krylov.Correction.RFCUniformParameters
import krylov.Correction.ObservedPrefixModels
import krylov.Correction.GatedRFCComparison

/-!
Article: main_krylov, thm:UCq and thm:UCg(iii), actual nonstagnating model tests.
Use: Connect the completed real finite-prefix induction to the original
measured spectral test, actual defect gate and step-normalized model.
Source: constructed common uniform allowances, proved actual recorded-prefix
bounds and the genuine observed-window model conditioning theorem.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- One common radius and constants before every reference and run make the actual nonstagnating preterminal spectral gates pass and every nonzero-direction model satisfy the original linear normalized conditioning bound.
Use: Transfer complete genuine uniform model and gate statements to ordinary RFC.
Article: main_krylov, thm:UCq and thm:UCg(iii).
Proof: The actual finite-prefix induction supplies nonzero old steps and linear normalized angles. The genuine global recording induction derives every real measured relative secant error. The original observed-window conditioning theorem proves each actual inverse, defect and spectral decision and the true normalized model bound. Genuine preterminal search domains remove the nonzero-direction premise before the last iteration.
-/
theorem gated_uniform_nonstagnating_models (n : ℕ) (hn : 2≤n) (κ γ : ℝ)
    (hκ : 1≤κ) (hγ : 0<γ) (hγ1 : γ<1) :
    ∃ M₀ ε₀ Cₘ : ℝ, 0<M₀ ∧ 0<ε₀ ∧ 0<Cₘ ∧
      ∀ (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (g : EuclideanSpace ℝ (Fin n)) (ε : ℝ), 0<ε → ε≤ε₀ →
      ‖cgCanonicalError base g 0‖≤1 → (∀ i<n, CG.gradient (cgOperator base) g i≠0) →
      M₀*ε≤‖cgCanonicalError base g (n-2)‖ →
      (∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      (∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) →
      let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
      let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
      (∀ k<n-1,
        let H := methodRun m A B g k
        let W := selectedWindow fullMemory H
        let d := m.direction H
        spectralGate γ ((d,A k d)::W)) ∧
      (∀ k<n,
        let H := methodRun m A B g k
        let W := selectedWindow fullMemory H
        let d := m.direction H
        d≠0 →
        IsUnit (crossGram (windowImages W) (windowSteps W)).det ∧
        spectralGate γ ((d,A k d)::W) ∧ ‖windowDefect W‖<1 ∧
        ‖rescaleModel (pairModel (Fin.cons (R d) (primalWindow base (windowSteps W)))
          (Fin.cons (canonicalOperator base (A k) (R d)) (dualWindow base (windowImages W))))
          (fun i => ‖(Fin.cons (R d) (primalWindow base (windowSteps W)) : Fin (W.length+1) → EuclideanSpace ℝ (Fin n)) i‖⁻¹)-1‖≤Cₘ*ε) := by
  obtain ⟨K,C,L,M,δ,hK,hC,hL,hM,hδ,hgrowth,hallow,hMgrad,hMstep,hsmall⟩ :=
    rfc_uniform_prefix_parameters n κ γ hκ hγ hγ1
  let a := rfcLinearAngleConstant n K C
  have hK0 : 0≤K := by rw [hK]; exact mul_nonneg (by norm_num) (gatedCorrectionConstant_nonneg n γ)
  have ha : 0<a := rfcLinearAngleConstant_pos n hK0 hC.le
  let Cₘ := (n : ℝ)*(a+1+K)+1
  have hCₘ : 0<Cₘ := by dsimp only [Cₘ]; positivity
  refine ⟨M,δ,Cₘ,hM,hδ,hCₘ,?_⟩
  intro base hb μ hμ hspec A B g ε hε he hinit hpre hN hA hB
  let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  obtain ⟨hhalf,hrecord,hangle,hF,hProj⟩ := hsmall ε hε.le he
  have hpref := gated_nonstagnating_prefix base hb hn γ hγ hγ1 hμ hκ hK hC.le hL hε hhalf
    hspec hgrowth hallow hrecord hangle hF hProj hMgrad hMstep A B g hinit hpre hN hA hB
  have hrec := gated_uniform_recorded_bounds base hb fullMemory γ hγ A B g n hε.le hA hB
    (by simpa only [hK] using hrecord.1) (by simpa only [hK] using hrecord.2.1)
    (by simpa only [hK] using hrecord.2.2)
  have hη : 0≤(1+K)*ε := by positivity
  have hQ := rfcRelativeCorrectionConstant_nonneg n hK0 hC.le
  have hηa : (1+K)*ε≤(a*ε)/2 := by
    dsimp only [a,rfcLinearAngleConstant]
    nlinarith
  have hmodels (k : ℕ) (hk : k<n) (hd : m.direction (methodRun m A B g k)≠0) := by
    let H := methodRun m A B g k
    let W := selectedWindow fullMemory H
    have hlen : W.length=k := by dsimp only [W,H]; rw [fullWindow_methodRun,executedPairs_length]
    have hpr := (hpref k (by omega)).2.1
    have hy : ∀ i, ‖dualWindow base (windowImages W) i-primalWindow base (windowSteps W) i‖≤
        ((1+K)*ε)*‖primalWindow base (windowSteps W) i‖ :=
      selectedWindow_pair_bound fullMemory m A B g k R J _ (fun i hi => by
        simpa only [hK] using hrec.2 i (hi.trans hk))
    exact observed_prefix_model_conditioning base hb W H.gradient (A k) (by omega : 1≤n)
      (by rw [hlen]; omega) (mul_nonneg ha.le hε.le) hη (by nlinarith : ε≤(1+K)*ε) hηa hγ.le hγ1
      hangle hpr.1 hpr.2.1 hy hd (hA k hk)
  dsimp only
  refine ⟨?_,?_⟩
  · intro k hk
    have hdom := (hpref (k+1) (by omega)).1 k (Nat.lt_succ_self k)
    have hd : m.direction (methodRun m A B g k)≠0 := by
      intro hz
      have hc := hdom.2
      rw [hz,map_zero,inner_zero_left] at hc
      exact hc rfl
    exact (hmodels k (by omega) hd).2.1
  · intro k hk hd
    have hm := hmodels k hk hd
    refine ⟨hm.1,hm.2.1,hm.2.2.1,?_⟩
    apply hm.2.2.2.trans
    have hlen : (selectedWindow fullMemory (methodRun m A B g k)).length=k := by
      rw [fullWindow_methodRun,executedPairs_length]
    rw [hlen]
    have hk' : ((k+1 : ℕ) : ℝ)≤n := by exact_mod_cast (show k+1≤n by omega)
    have hb := mul_le_mul_of_nonneg_right hk' (show 0≤a+1+K by positivity)
    have ht := mul_le_mul_of_nonneg_right hb hε.le
    dsimp only [Cₘ]
    nlinarith

end
end krylov.Correction
