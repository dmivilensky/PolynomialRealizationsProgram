import krylov.Correction.RFCUniformConstants
import krylov.Correction.RecordedPrefixReindex
import krylov.Stability.ActualObservedSearch

/-!
Article: main_krylov, thm:UCq, actual nonstagnating finite-prefix induction.
Use: Derive true observed inverse/search domains, linear normalized angles,
quadratic projected residuals and uniform recorded-step stability under (N).
Source: genuine measured gated execution, constructed finite error allowances,
weighted observed CG search stability and the actual projected-residual recurrence.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

set_option maxHeartbeats 1200000 in
/-- Condition (N) derives every actual preterminal search domain, linear angle, quadratic projected residual and uniform recorded-step bound, together with a linear relative correction-to-line allowance.
Use: Derive actual ordinary-RFC stability and quadratic relative pair contamination from original measured data.
Article: main_krylov, thm:UCq.
Proof: Induct over the genuine observed history. Derive each old inverse from the actual normalized cross Gram, exclude a zero current direction by the real coercive projected-gradient bound and (N), and apply genuine weighted search stability. The true line lower bound closes the measured linear-angle and residual step. Retain its actual relative correction estimate alongside the monotone recorded-step recurrence. No trajectory bound or inverse domain is supplied as a premise.
-/
theorem gated_nonstagnating_prefix_with_corrections (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1) {μ κ K C L M₀ ε : ℝ}
    (hμ : 0<μ) (hκ : 1≤κ) (hKdef : K=2*gatedCorrectionConstant n γ)
    (hC : 0≤C) (hL : 0≤L) (hε : 0<ε) (hεhalf : ε≤1/2)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ)
    (hLgrowth : (gatedGrowthConstant n γ)^n≤L)
    (hallow : 4*gatedProjectedConstant n K*(Real.sqrt n*(2+K))*L≤C)
    (hrecord : (1+K)*ε≤1/2 ∧ (n : ℝ)*((1+K)*ε)≤γ/4 ∧ (n : ℝ)*((1+K)*ε)≤1)
    (hangle : (n : ℝ)*(rfcLinearAngleConstant n K C*ε)≤(1-γ)/8)
    (hsmall : gatedProjectedConstant n K*ε≤1/2)
    (hProj : 4*Real.sqrt n*((1+K)*ε)≤1/2)
    (hM : (n : ℝ)*(rfcUniformStepConstant n κ K C L n+
      (1+K)*(rfcUniformStepConstant n κ K C L n+1))+4*κ*C<M₀)
    (hMstep : Real.sqrt κ*(rfcUniformStepConstant n κ K C L n+2)≤M₀)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (hinit : ‖cgCanonicalError base g 0‖≤1)
    (hpre : ∀ i<n, CG.gradient (cgOperator base) g i≠0)
    (hN : M₀*ε≤‖cgCanonicalError base g (n-2)‖)
    (hA : ∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hB : ∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) :
    let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    ∀ k≤n-1, gatedFullRunDefined γ A B g k ∧
      recordedPrefixBound (rfcLinearAngleConstant n K C*ε) C ε
        (primalWindow base (windowSteps (selectedWindow fullMemory (methodRun m A B g k))))
        (J (probedGradient m A B g k)) ∧
      ∀ i<k, ‖R (probedStep m A B g i)-canonicalCGStep base g i‖≤rfcUniformStepConstant n κ K C L k*ε ∧
        ‖R (probedPhase m A B g i).movement‖≤(rfcRelativeCorrectionConstant n K C*ε)*‖R (gatedObservedLineStep γ A B g i)‖ := by
  let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let W := fun i => selectedWindow fullMemory (methodRun m A B g i)
  let a := rfcLinearAngleConstant n K C
  let Q := rfcRelativeCorrectionConstant n K C
  let S := rfcUniformStepConstant n κ K C L
  let D := (n : ℝ)*(S n+(1+K)*(S n+1))
  have hκ0 : 0≤κ := by linarith
  have hK : 0≤K := by rw [hKdef]; exact mul_nonneg (by norm_num) (gatedCorrectionConstant_nonneg n γ)
  have ha : 0<a := rfcLinearAngleConstant_pos n hK hC
  have hQ : 0≤Q := rfcRelativeCorrectionConstant_nonneg n hK hC
  have hS i : 0≤S i := rfcUniformStepConstant_nonneg n hκ0 hK hC hL i
  have hSmono : Monotone S := rfcUniformStepConstant_monotone n hκ0 hK hC hL
  have hn1 : 1≤n := by omega
  have hη : 0≤(1+K)*ε := by positivity
  have hηa : (1+K)*ε≤(a*ε)/2 := by
    dsimp only [a,rfcLinearAngleConstant]
    change (1+K)*ε≤(2*(1+K)+2*Q)*ε/2
    nlinarith
  have hmarg := uniform_gate_margins hn1 (le_refl n) hγ.le hγ1 (mul_nonneg ha.le hε.le) hη hηa hangle
  have hGramSmall : ((n : ℝ)*a)*ε≤1/2 := by nlinarith [mul_nonneg (Nat.cast_nonneg n) hη]
  have hrec := gated_uniform_recorded_bounds base hb fullMemory γ hγ A B g n hε.le hA hB
    (by simpa only [hKdef] using hrecord.1) (by simpa only [hKdef] using hrecord.2.1)
    (by simpa only [hKdef] using hrecord.2.2)
  have hgrowth := gated_uniform_prefix_growth base hb fullMemory γ hγ A B g n hε.le hA hB
    (by simpa only [hKdef] using hrecord.1) (by simpa only [hKdef] using hrecord.2.1)
    (by simpa only [hKdef] using hrecord.2.2)
  have hbase : ‖cgOperator base‖≤κ*μ := (cgOperator_norm_le base hb (by positivity : 0≤μ*κ)
    (fun i => (hspec i).2)).trans_eq (by ring)
  have hcgrow : 1≤gatedGrowthConstant n γ := by
    unfold gatedGrowthConstant
    have ht : 0≤10*(n : ℝ)/γ := by positivity
    linarith
  have hinit' : ‖J g‖≤1 := hinit
  have hgrowthL i (hi : i≤n) : ‖J (probedGradient m A B g i)‖≤L := by
    calc
      _ ≤ (gatedGrowthConstant n γ)^i*‖J g‖ := hgrowth.2 i hi
      _ ≤ (gatedGrowthConstant n γ)^n*1 := mul_le_mul (pow_le_pow_right₀ hcgrow hi) hinit' (norm_nonneg _) (by positivity)
      _ ≤ L := by rw [mul_one]; exact hLgrowth
  have hyall i (hi : i<n) : ‖J (probedSecant m A B g i)-R (probedStep m A B g i)‖≤((1+K)*ε)*‖R (probedStep m A B g i)‖ := by
    simpa only [hKdef] using hrec.2 i hi
  have hlen i : (W i).length=i := by dsimp only [W]; rw [fullWindow_methodRun,executedPairs_length]
  have hpref : ∀ k≤n-1,
      gatedFullRunDefined γ A B g k ∧
      recordedPrefixBound (a*ε) C ε (primalWindow base (windowSteps (W k))) (J (probedGradient m A B g k)) ∧
      ∀ i<k, ‖R (probedStep m A B g i)-canonicalCGStep base g i‖≤S k*ε ∧
        ‖R (probedPhase m A B g i).movement‖≤(Q*ε)*‖R (gatedObservedLineStep γ A B g i)‖ := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun i hi => (by omega),?_,fun i hi => (by omega)⟩
      have he : primalWindow base (windowSteps (W 0))=(fun i : Fin 0 => Fin.elim0 i) := by
        funext i; exact Fin.elim0 i
      rw [he]
      exact recordedPrefixBound_empty (a*ε) C ε hC (J g)
    | succ k ih =>
      intro hk
      have hkN : k<n := by omega
      have hprev := ih (by omega)
      have hk2 : k≤n-2 := by omega
      have hSk := hS k
      let H := methodRun m A B g k
      let s := primalWindow base (windowSteps (W k))
      let y := dualWindow base (windowImages (W k))
      let G := J H.gradient
      let d := R (m.direction H)
      let Ac := canonicalOperator base (A k)
      let Bc := canonicalOperator base (B k)
      let P := gatedArrayPhase γ s y G d (Ac d) Bc
      let line := lineLength G d (Ac d) • d
      have hchrono : recordedPrefixBound (a*ε) C ε
          (fun i : Fin k => R (probedStep m A B g i.val)) G := by
        have ho := hprev.2.1
        change recordedPrefixBound (a*ε) C ε
          (fun i : Fin (W k).length => R (windowSteps (W k) i)) G at ho
        dsimp only [W] at ho
        rw [fullWindow_methodRun] at ho
        exact (recordedPrefixBound_executed_chronological _ _ R G k (a*ε) C ε).mp ho
      have hGram : ‖crossGram
          (unitWindow (fun i : Fin k => R (probedStep m A B g i.val)))
          (unitWindow (fun i : Fin k => R (probedStep m A B g i.val)))-1‖≤((n : ℝ)*a)*ε := by
        have ht := unitGram_deviation _ (unitWindow_norm _ hchrono.1) (mul_nonneg ha.le hε.le) hchrono.2.1
        apply ht.trans
        have hk' : (k : ℝ)≤n := by exact_mod_cast hkN.le
        nlinarith [mul_nonneg ha.le hε.le]
      have hsolveSmall : ((n : ℝ)*a)*ε+(k : ℝ)*((1+K)*ε)≤1/2 := by
        have hk' : (k : ℝ)≤n := by exact_mod_cast hkN.le
        have ht := mul_le_mul_of_nonneg_right hk' hη
        nlinarith [hmarg.2.1]
      have hProjk : 4*Real.sqrt k*((1+K)*ε)≤1/2 :=
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hkN.le))
          (by norm_num : (0 : ℝ)≤4)) hη).trans hProj
      have hCsolve := full_observed_solve_from_canonical base hb m A B g k hη
        (fun i hi => hchrono.1 ⟨i,hi⟩) (fun i hi => hyall i (hi.trans hkN)) hGram hsolveSmall
      have hgrad := probed_canonical_gradient_bound base hb m A B g k hε.le (by linarith)
        (hS k) (by positivity : 0≤1+K) hinit (fun i hi => (hprev.2.2 i hi).1) (fun i hi => hyall i (hi.trans hkN))
      have hDk : (k : ℝ)*(S k+(1+K)*(S k+1))≤D := by
        have hlin : S k+(1+K)*(S k+1)≤S n+(1+K)*(S n+1) := by
          have hm := hSmono hkN.le
          nlinarith
        exact mul_le_mul (by exact_mod_cast hkN.le) hlin (by positivity) (Nat.cast_nonneg n)
      have hgradD : ‖G-cgCanonicalError base g k‖≤D*ε := hgrad.trans (mul_le_mul_of_nonneg_right hDk hε.le)
      have hGstrict : 4*κ*‖projectedResidual
          (unitWindow (fun i : Fin k => R (probedStep m A B g i.val))) G‖<‖G‖ := by
        have he := (hN.trans (cgError_antitone base hb g hk2)).trans
          ((norm_le_norm_sub_add (cgCanonicalError base g k) G).trans
            (add_le_add (by simpa only [norm_sub_rev] using hgradD) (le_refl _)))
        have hr := mul_le_mul_of_nonneg_left hchrono.2.2 (by positivity : 0≤4*κ)
        have hm := mul_lt_mul_of_pos_right hM hε
        have he1 : ε≤1 := by linarith
        have hs := mul_le_mul_of_nonneg_left he1 (by positivity : 0≤4*κ*C*ε)
        change D+4*κ*C<M₀ at hM
        nlinarith only [he,hr,hm,hs]
      have hd : d≠0 := by
        change R (windowDirection (selectedWindow fullMemory H) H.gradient)≠0
        dsimp only [H]
        rw [fullWindow_methodRun]
        exact observed_canonical_direction_nonzero base hb _ _ _ k hμ hκ0
          (fun i => (hspec i).1) hbase (hGram.trans hGramSmall) hGstrict
      have hdphys : m.direction H≠0 := by intro hz; apply hd; simp only [d,hz,map_zero]
      have hcurv : inner ℝ (m.direction H) (A k (m.direction H))≠0 :=
        (canonical_curvature_positive base hb (A k) (m.direction H) hdphys ((hA k hkN).trans hεhalf)).ne'
      have hcurvc : inner ℝ d (Ac d)≠0 := by
        dsimp only [d,Ac]
        rw [canonicalOperator_primal base hb,← canonical_search_pairing base hb]
        exact hcurv
      have hlineerr := gated_observed_next_line_bound base hb γ A B g k hμ hκ (hS k)
        (mul_nonneg (Nat.cast_nonneg n) ha.le) (by positivity : 0≤1+K) hspec hinit
        (fun i hi => hpre i (by omega)) hε.le (by linarith) hεhalf hGramSmall hsolveSmall hProjk
        (fun i hi => hchrono.1 ⟨i,hi⟩) (fun i hi => hyall i (hi.trans hkN)) hGram hd (hA k hkN) (fun i hi => (hprev.2.2 i hi).1)
      have hnextAllowance := rfcUniformStepConstant_next_allowance n k hκ0 hK hC hL
      let F := observedCGStepConstant k κ (S k) ((k : ℝ)*(S k+(1+K)*(S k+1))) ((n : ℝ)*a) (1+K)
      have hF : 0≤F := observedCGStepConstant_nonneg k hκ0 (hS k) (by positivity) (by positivity) (by positivity)
      have hFbound : F≤S n := by
        have ht : F≤S (k+1) := by
          change F+2*Q*L≤S (k+1) at hnextAllowance
          linarith [mul_nonneg (by positivity : 0≤2*Q) hL]
        exact ht.trans (hSmono (by omega))
      have hlineerrMax : ‖R (gatedObservedLineStep γ A B g k)-canonicalCGStep base g k‖≤S n*ε :=
        hlineerr.trans (mul_le_mul_of_nonneg_right hFbound hε.le)
      have hactive : k<referenceAtomCount base hb g := by
        by_contra hh
        exact hpre k hkN ((cg_stopping_iff base hb g k).mpr (by omega))
      have hratio : ‖cgCanonicalError base g (n-2)‖≤Real.sqrt κ*‖canonicalCGStep base g k‖ := by
        simpa only [mul_div_cancel_left₀ _ hμ.ne'] using cgError_step_ratio base hb g hμ
          (by nlinarith : μ≤μ*κ) hspec hactive hk2
      have hsqrt : 0<Real.sqrt κ := Real.sqrt_pos.mpr (by linarith)
      have href : (S n+2)*ε≤‖canonicalCGStep base g k‖ := by
        apply (mul_le_mul_iff_right₀ hsqrt).mp
        calc
          _ = (Real.sqrt κ*(S n+2))*ε := by ring
          _ ≤ M₀*ε := mul_le_mul_of_nonneg_right hMstep hε.le
          _ ≤ _ := hN.trans hratio
      have hlinebig : ε≤‖R (gatedObservedLineStep γ A B g k)‖ := by
        have ht := norm_le_norm_sub_add (canonicalCGStep base g k) (R (gatedObservedLineStep γ A B g k))
        rw [norm_sub_rev] at ht
        nlinarith
      have hfields := probedGated_canonical_window_fields base hb fullMemory γ A B g k
      change P.movement=R (probedPhase m A B g k).movement ∧
        P.gradient=J (probedGradient m A B g (k+1)) ∧ line+P.movement=R (probedStep m A B g k) at hfields
      have hlineeq : line=R (gatedObservedLineStep γ A B g k) := by
        dsimp only [line,Ac,d]
        rw [canonicalOperator_primal base hb,canonical_lineLength base hb]
        change _=R (lineLength H.gradient (m.direction H) (A k (m.direction H)) • m.direction H)
        rw [map_smul]
      have hnext : recordedPrefixBound (a*ε) C ε (Fin.cons (line+P.movement) s) P.gradient ∧
          ‖P.movement‖≤(Q*ε)*‖line‖ := by
        by_cases hk0 : k=0
        · subst k
          have hp0 := gatedArrayPhase_empty γ s y G d (Ac d) Bc
          refine ⟨recordedPrefixBound_empty_step (a*ε) C ε γ hC s y Ac Bc G d hcurvc ?_,?_⟩
          · change 0<‖line‖
            rw [hlineeq]; exact hε.trans_le hlinebig
          · have hm0 : P.movement=0 := hp0.1
            rw [hm0,norm_zero]; positivity
        · have hsize : (W k).length+1≤n := by rw [hlen]; omega
          have hy : ∀ j, ‖y j-s j‖≤((1+K)*ε)*‖s j‖ := selectedWindow_pair_bound fullMemory m A B g k R J _
            (fun j hj => hyall j (hj.trans hkN))
          have ho (j : Fin (W k).length) : inner ℝ (y j) d=0 :=
            canonical_window_image_conjugacy base hb (W k) H.gradient hCsolve j
          have hrel : ‖P.movement‖≤K*‖line+P.movement‖ := by
            rw [hfields.2.2,hfields.1]
            apply (hrec.1 k hkN).trans
            apply mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [hKdef]
            have ht := gatedCorrectionConstant_nonneg n γ
            linarith
          exact recordedPrefixBound_linear_step s y Ac Bc G d (by rw [hlen]; omega) hn1 hsize hγ.le hγ1 hC hε hK
            (hgrowthL k hkN.le) hprev.2.1 (hA k hkN) (hB k hkN) hy ho hcurvc hangle hsmall hallow
            (by change ε≤‖line‖; rw [hlineeq]; exact hlinebig) hrel
      have hlinebound : ‖line‖≤2*L := (actual_line_norm_bound Ac G d (hA k hkN) hεhalf).trans
        (mul_le_mul_of_nonneg_left (hgrowthL k hkN.le) (by norm_num : (0 : ℝ)≤2))
      have hχ : ‖P.movement‖≤(2*Q*L)*ε := hnext.2.trans
        ((mul_le_mul_of_nonneg_left hlinebound (mul_nonneg hQ hε.le)).trans_eq (by ring))
      have hnewStep : ‖R (probedStep m A B g k)-canonicalCGStep base g k‖≤S (k+1)*ε := by
        rw [← hfields.2.2]
        have he : line+P.movement-canonicalCGStep base g k=(line-canonicalCGStep base g k)+P.movement := by abel
        rw [he]
        have heLine : ‖line-canonicalCGStep base g k‖≤F*ε := by rw [hlineeq]; exact hlineerr
        apply ((norm_add_le _ _).trans (add_le_add heLine hχ)).trans
        have ht := mul_le_mul_of_nonneg_right hnextAllowance hε.le
        calc
          _ = (F+2*Q*L)*ε := by ring
          _ ≤ _ := ht
      refine ⟨?_,?_,?_⟩
      · intro i hi
        by_cases he : i=k
        · subst i; exact ⟨hCsolve,hcurv⟩
        · exact hprev.1 i (by omega)
      · rw [show W (k+1)=(probedStep m A B g k,probedSecant m A B g k)::W k from full_observed_window_next m A B g k,
          windowSteps_cons]
        have hmap : primalWindow base (Fin.cons (probedStep m A B g k) (windowSteps (W k)))=
            Fin.cons (R (probedStep m A B g k)) s := by
          funext j; exact Fin.cases rfl (fun _ => rfl) j
        rw [hmap,← hfields.2.2,← hfields.2.1]
        exact hnext.1
      · intro i hi
        by_cases he : i=k
        · subst i
          refine ⟨hnewStep,?_⟩
          rw [← hfields.1,← hlineeq]
          exact hnext.2
        · exact ⟨((hprev.2.2 i (by omega)).1).trans
            (mul_le_mul_of_nonneg_right (hSmono (Nat.le_succ k)) hε.le),
            (hprev.2.2 i (by omega)).2⟩
  exact hpref


/-- Every actual nonstagnating prefix has its genuine observed inverse/search domains, linear normalized angles, quadratic projected residual and uniform recorded-step comparison.
Use: Apply the complete actual induction while hiding its extra relative-correction conclusion.
Article: main_krylov, thm:UCq.
Proof: Take the corresponding proved fields of the stronger original finite-prefix theorem.
-/
theorem gated_nonstagnating_prefix (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (hn : 2≤n) (γ : ℝ) (hγ : 0<γ) (hγ1 : γ<1) {μ κ K C L M₀ ε : ℝ}
    (hμ : 0<μ) (hκ : 1≤κ) (hKdef : K=2*gatedCorrectionConstant n γ)
    (hC : 0≤C) (hL : 0≤L) (hε : 0<ε) (hεhalf : ε≤1/2)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ)
    (hLgrowth : (gatedGrowthConstant n γ)^n≤L)
    (hallow : 4*gatedProjectedConstant n K*(Real.sqrt n*(2+K))*L≤C)
    (hrecord : (1+K)*ε≤1/2 ∧ (n : ℝ)*((1+K)*ε)≤γ/4 ∧ (n : ℝ)*((1+K)*ε)≤1)
    (hangle : (n : ℝ)*(rfcLinearAngleConstant n K C*ε)≤(1-γ)/8)
    (hsmall : gatedProjectedConstant n K*ε≤1/2)
    (hProj : 4*Real.sqrt n*((1+K)*ε)≤1/2)
    (hM : (n : ℝ)*(rfcUniformStepConstant n κ K C L n+
      (1+K)*(rfcUniformStepConstant n κ K C L n+1))+4*κ*C<M₀)
    (hMstep : Real.sqrt κ*(rfcUniformStepConstant n κ K C L n+2)≤M₀)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (hinit : ‖cgCanonicalError base g 0‖≤1)
    (hpre : ∀ i<n, CG.gradient (cgOperator base) g i≠0)
    (hN : M₀*ε≤‖cgCanonicalError base g (n-2)‖)
    (hA : ∀ i<n, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε)
    (hB : ∀ i<n, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤ε) :
    let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    ∀ k≤n-1, gatedFullRunDefined γ A B g k ∧
      recordedPrefixBound (rfcLinearAngleConstant n K C*ε) C ε
        (primalWindow base (windowSteps (selectedWindow fullMemory (methodRun m A B g k))))
        (J (probedGradient m A B g k)) ∧
      ∀ i<k, ‖R (probedStep m A B g i)-canonicalCGStep base g i‖≤rfcUniformStepConstant n κ K C L k*ε := by
  have h := gated_nonstagnating_prefix_with_corrections base hb hn γ hγ hγ1 hμ hκ hKdef hC hL hε hεhalf
    hspec hLgrowth hallow hrecord hangle hsmall hProj hM hMstep A B g hinit hpre hN hA hB
  dsimp only
  intro k hk
  exact ⟨(h k hk).1,(h k hk).2.1,fun i hi => ((h k hk).2.2 i hi).1⟩

end
end krylov.Correction
