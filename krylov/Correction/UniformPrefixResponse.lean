import krylov.Correction.OrdinaryTerminalResponse
import krylov.Correction.OrdinaryTerminalPrefix
import krylov.Correction.TerminalObservedGeometry
import krylov.Correction.OrdinaryObservedLine
import krylov.Correction.TerminalWeightedFlags

/-!
Article: main_krylov, thm:UCq, shared genuine uniform terminal assembly.
Use: Reuse the same measured terminal reconstruction for the nonstagnating
prefix and the exceptional small-dimensional prefix, with every prefix bound
derived separately from its real executor.
Source: actual recorded-pair geometry, observed search stability, true
reference-weighted flags and the original finite-source terminal identity.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
  krylov.Variation krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

/-- The actual observed preterminal data needed for uniform terminal reconstruction, stated entirely in the original ordinary executor.
Use: Share already proved prefix estimates between the (N) and low-dimensional cases; this predicate contains no terminal response estimate.
Article: main_krylov, thm:UCq.
-/
def ordinaryTerminalPrefixBounds {n : ℕ} (base : Matrix (Fin n) (Fin n) ℝ)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (a Cr D Cξ Cm ε : ℝ) : Prop :=
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
  let R := cgOperator (metricRoot base)
  let J := cgOperator (metricRoot base)⁻¹
  activeObservedModelBounds base m A B g n (1/2) Cm ε ∧
    (∀ j≤n-1, methodRun (gatedMethod fullMemory (1/2)) A B g j=methodRun m A B g j) ∧
    recordedPrefixBound (a*ε) Cr ε (fun i : Fin (n-1) => R (probedStep m A B g i.val))
      (J (probedGradient m A B g (n-1))) ∧
    ∀ i<n-1, ‖R (probedStep m A B g i)-canonicalCGStep base g i‖≤D*ε ∧
      ‖J (probedSecant m A B g i)-canonicalOperator base (A i) (R (probedStep m A B g i))‖≤
        Cξ*ε^2*‖R (probedStep m A B g i)‖

set_option maxHeartbeats 1600000 in
/-- Any derived uniform tube for the genuine ordinary observed prefix yields the original full-source cubic expansion with constants chosen before every reference and scenario.
Use: Share one quantitative last-cycle argument between the nonstagnating and three-dimensional exceptional inductions.
Article: main_krylov, thm:UCq.
Proof: Fix every numerical inverse margin before the data. Actual old conjugacy and measured secant errors give the full terminal Gram and model bounds. The genuine observed search controls the real last line without a lower reference energy; true reference-weighted flags compare its exact staircase with CG. Apply the proved original-source terminal response identity and convert the operator allowance to the primitive finite-source budget. The supplied predicate restricts only earlier observed data, not the terminal conclusion.
-/
theorem ordinary_uniform_source_response_unit_of_prefix (k : ℕ) (hk : 0<k) (κ : ℝ) (hκ : 1≤κ)
    (condition : Matrix (Fin (k+1)) (Fin (k+1)) ℝ → EuclideanSpace ℝ (Fin (k+1)) → ℝ → Prop)
    {δ a Cr D Cξ Cm : ℝ} (hδ : 0<δ) (ha : 0<a) (hCr : 0<Cr) (hD : 0<D) (hCξ : 0<Cξ)
    (hprefix : ∀ (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
        (g : EuclideanSpace ℝ (Fin (k+1))) (ε : ℝ), A 0=cgOperator base → 0<ε → ε≤δ →
      ‖cgCanonicalError base g 0‖≤1 → (∀ i<k+1, CG.gradient (cgOperator base) g i≠0) →
      condition base g ε →
      (∀ i<k+1, ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1)))‖≤ε) →
      (∀ i<k+1, ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1)))‖≤ε) →
      ordinaryTerminalPrefixBounds base A B g a Cr D Cξ Cm ε) :
    ∃ ω₀ C : ℝ, 0<ω₀ ∧ 0<C ∧
      ∀ (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (μ : ℝ), 0<μ →
      (∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ) →
      ∀ (Θ : symmetricScenarios (k+1) (k+1)) (g : EuclideanSpace ℝ (Fin (k+1))) (ω : ℝ),
      0<ω → ω≤ω₀ → ‖cgCanonicalError base g 0‖=1 → referenceAtomCount base hb g=k+1 →
      condition base g ((((k+1 : ℕ) : ℝ)+1)*ω) →
      (∀ i, ‖Θ.val.1 i‖≤ω) → (∀ i, ‖Θ.val.2 i‖≤ω) →
      let A := scenarioProbe base Θ.val
      let B := scenarioCorrection base Θ.val
      let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
      m.direction (methodRun m A B g k)≠0 →
      ‖cgOperator (metricRoot base)⁻¹ (probedGradient m A B g (k+1))+
        ‖cgCanonicalError base g k‖ • staircaseOperator base g
          (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
          (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1))‖≤C*ω^3 := by
  let N : ℝ := ((k+1 : ℕ) : ℝ)
  let K := 1+Cξ
  let Gc := N*(a+K)
  let Bc := N*(a+2*K)
  let Cl := observedCGStepConstant k κ D ((k : ℝ)*(D+K*(D+1))) ((k : ℝ)*a) K
  have hK : 1≤K := by dsimp only [K]; linarith
  have hK0 : 0≤K := by linarith
  have hGc : 0≤Gc := by dsimp only [Gc]; positivity
  have hBc : 0≤Bc := by dsimp only [Bc]; positivity
  have hCl : 0≤Cl := by
    dsimp only [Cl]
    exact observedCGStepConstant_nonneg k (by linarith) hD.le (by positivity) (by positivity) hK0
  let L := 1+Cl
  let Hc := 3*Gc+4*N*Real.sqrt κ*D
  let e := 2*Real.sqrt (k+1)*(Cr+Cξ*L)
  let d := 4*N+1
  let r := 2*N*L
  let Cc := ((8*N*Cξ+d*(8*Bc+4*Gc))*(r+e)+d*e)+
    ((4*N+1)*N*(2*N*Cl+Hc)+8*N^2*Hc)
  have hL : 0≤L := by dsimp only [L]; positivity
  have hHc : 0≤Hc := by dsimp only [Hc]; positivity
  have hCc : 0≤Cc := by dsimp only [Cc,e,d,r]; positivity
  let Rn := Bc+4*Real.sqrt k*K+1
  let ρ := min δ (1/(2*Rn))
  let Jn := N+1
  -- All scalar margins are fixed before the reference, spectral scale and source.
  have hRn : 0<Rn := by dsimp only [Rn]; positivity
  have hρ : 0<ρ := lt_min hδ (by positivity)
  have hJn : 0<Jn := by dsimp only [Jn,N]; positivity
  refine ⟨ρ/Jn,(Cc+1)*Jn^3,div_pos hρ hJn,by positivity,?_⟩
  intro base hb μ hμ hspec Θ g ω hω he hinit hcount hN hE hF
  dsimp only
  intro hdir
  let A := scenarioProbe base Θ.val
  let B := scenarioCorrection base Θ.val
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
  let P := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let s : Fin k → EuclideanSpace ℝ (Fin (k+1)) := fun i => P (probedStep m A B g i.val)
  let G := J (probedGradient m A B g k)
  let ε := Jn*ω
  have hε : 0<ε := mul_pos hJn hω
  have heρ : ε≤ρ := by
    have ht := (le_div_iff₀ hJn).mp he
    dsimp only [ε]
    nlinarith only [ht]
  have hep : ε≤δ := heρ.trans (min_le_left _ _)
  have hsmall : ε*(2*Rn)≤1 := (le_div_iff₀ (by positivity : 0<2*Rn)).mp (heρ.trans (min_le_right _ _))
  have hεhalf : ε≤1/2 := by
    dsimp only [Rn] at hsmall
    nlinarith [mul_nonneg hBc hε.le,mul_nonneg (show 0≤4*Real.sqrt k*K by positivity) hε.le]
  have hεone : ε≤1 := by linarith
  have hBhalf : Bc*ε≤1/2 := by
    dsimp only [Rn] at hsmall
    nlinarith [mul_nonneg (show 0≤4*Real.sqrt k*K by positivity) hε.le]
  have hProj : 4*Real.sqrt k*(K*ε)≤1/2 := by
    dsimp only [Rn] at hsmall
    nlinarith [mul_nonneg hBc hε.le]
  have hGB : Gc≤Bc := by
    dsimp only [Gc,Bc]
    nlinarith [mul_nonneg (show 0≤N by dsimp only [N]; positivity) hK0]
  have hGhalf : Gc*ε≤1/2 := (mul_le_mul_of_nonneg_right hGB hε.le).trans hBhalf
  have hOldGc : (k : ℝ)*a+(k : ℝ)*K≤Gc := by
    dsimp only [Gc,N]
    push_cast
    nlinarith only [ha.le,hK0]
  have hOldSolve : ((k : ℝ)*a)*ε+(k : ℝ)*(K*ε)≤1/2 := by
    have ht := (mul_le_mul_of_nonneg_right hOldGc hε.le).trans hGhalf
    nlinarith only [ht]
  have hOldHalf : ((k : ℝ)*a)*ε≤1/2 := by
    have hp : 0≤(k : ℝ)*(K*ε) := by positivity
    linarith
  have hωε : ω≤ε := by
    dsimp only [ε,Jn]
    nlinarith [mul_nonneg (show 0≤N by dsimp only [N]; positivity) hω.le]
  have hA i (hi : i<k+1) : ‖canonicalOperator base (A i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1)))‖≤ε :=
    (scenario_canonical_operator_budgets base hb Θ.val hω.le hE hF i hi).1
  have hB i (hi : i<k+1) : ‖canonicalOperator base (B i)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1)))‖≤ε :=
    (scenario_canonical_operator_budgets base hb Θ.val hω.le hE hF i hi).2
  have hpre i (hi : i<k+1) : CG.gradient (cgOperator base) g i≠0 := cg_nonstagnation base hb g i (by omega)
  have hA0 : A 0=cgOperator base := by
    simp only [A,scenarioProbe,canonicalFCPath,cumulativeDrift,range_zero,sum_empty,
      Matrix.mul_zero,Matrix.zero_mul,map_zero,one_smul,add_zero]
  have hp := hprefix base hb μ hμ hspec A B g ε hA0 hε hep hinit.le hpre hN hA hB
  dsimp only [ordinaryTerminalPrefixBounds] at hp
  -- Use only genuine preterminal data; no terminal expansion is a prefix input.
  have hpr : recordedPrefixBound (a*ε) Cr ε s G := hp.2.2.1
  have hs i (hi : i<k) : P (probedStep m A B g i)≠0 := hpr.1 ⟨i,hi⟩
  have hstep i (hi : i<k) : ‖P (probedStep m A B g i)-canonicalCGStep base g i‖≤D*ε := (hp.2.2.2 i hi).1
  have hxi i (hi : i<k) : ‖J (probedSecant m A B g i)-canonicalOperator base (A i) (P (probedStep m A B g i))‖≤
      Cξ*ε^2*‖P (probedStep m A B g i)‖ := (hp.2.2.2 i hi).2
  have hpair i (hi : i<k) : ‖J (probedSecant m A B g i)-P (probedStep m A B g i)‖≤K*ε*‖P (probedStep m A B g i)‖ :=
    observed_pair_error_of_quadratic_contamination (canonicalOperator base (A i)) _ _ hCξ.le hε.le hεone (hA i (by omega)) (hxi i hi)
  have hmodels := hp.1 k (by omega) hdir
  have hd : P (probedDirection m A B g k)≠0 := by
    intro hz
    have hc := canonical_primal_dual_cancel base hb (probedDirection m A B g k)
    change J (P (probedDirection m A B g k))=probedDirection m A B g k at hc
    rw [hz,map_zero] at hc
    exact hdir hc.symm
  have hcurv : inner ℝ (probedDirection m A B g k) (A k (probedDirection m A B g k))≠0 :=
    (canonical_curvature_positive base hb (A k) _ hdir ((hA k (by omega)).trans hεhalf)).ne'
  have hg := ordinary_terminal_observed_geometry base hb A B g ha.le hK hCξ.le hε.le hs hd hmodels.1
    hpr.2.1 hpair hxi (hA k (by omega))
  dsimp only at hg
  let S := primalWindow base ((probedStepBasis m A B g k) ∘ Fin.revPerm)
  let t := unitWindow S
  let z := rescaleWindow (dualWindow base ((probedImageBasis m A B g k) ∘ Fin.revPerm)) (fun i => ‖S i‖⁻¹)
  have hOldGram : ‖crossGram (unitWindow s) (unitWindow s)-1‖≤((k : ℝ)*a)*ε :=
    (unitGram_deviation (unitWindow s) (unitWindow_norm s hpr.1) (mul_nonneg ha.le hε.le) hpr.2.1).trans_eq (by ring)
  have hline := ordinary_observed_next_line_bound base hb A B g k hμ hκ hD.le
    (mul_nonneg (Nat.cast_nonneg k) ha.le) hK0 hspec hinit.le (fun i hi => hpre i (by omega))
    hε.le hεone hεhalf hOldHalf hOldSolve hProj hp.2.1 hs hpair hOldGram hd (hA k (by omega)) hstep
  -- The last line is bounded above, with no lower bound on its CG energy.
  have hreference : ‖canonicalCGStep base g k‖≤1 := by
    rw [← terminal_step_error_norm base hb g hcount.ge]
    exact (cgError_antitone base hb g (show 0≤k by omega)).trans hinit.le
  have hlineNorm : ‖P (fullLineStep 1 A B g k)‖≤L := by
    have ht := (norm_le_norm_sub_add (P (fullLineStep 1 A B g k)) (canonicalCGStep base g k)).trans (add_le_add hline hreference)
    have hm := mul_le_mul_of_nonneg_left hεone hCl
    dsimp only [L]
    linarith
  have hcoord := normalized_chronological_steps base m A B g k
  change t=Fin.snoc (unitWindow s) (NormedSpace.normalize (P (probedDirection m A B g k))) at hcoord
  have htOld (i : Fin (k+1)) (hi : i.val<k) : t i=NormedSpace.normalize (P (probedStep m A B g i.val)) := by
    let j : Fin k := ⟨i.val,hi⟩
    have hij : j.castSucc=i := Fin.ext rfl
    rw [← hij,hcoord,Fin.snoc_castSucc]
    rfl
  have hflags := terminal_recorded_weighted_flags base hb g hcount hμ hκ hspec hinit.le t
    (fun i => P (probedStep m A B g i)) hD.le hε.le hg.2.1 hGhalf
    (fun i hi => hs i (by omega)) (fun i hi => htOld i (by omega)) (fun i hi => hstep i (by omega))
  simp only [Nat.add_sub_cancel] at hflags
  -- The original finite increment arrays supply the real staircase budgets.
  have hbudget : (∑ l ∈ range (k+1), ‖matrixSequenceExtension k Θ.val.1 l‖)≤N*ε := by
    calc
      _ ≤ ∑ _l ∈ range (k+1), ε := sum_le_sum fun l _ =>
        (matrixSequenceExtension_norm_le k l Θ.val.1 hω.le hE).trans hωε
      _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul]; rfl
  have hFbound : ‖matrixSequenceExtension (k+1) Θ.val.2 k‖≤1*ε := by
    simpa only [one_mul] using (matrixSequenceExtension_norm_le (k+1) k Θ.val.2 hω.le hF).trans hωε
  have hresponse := ordinary_terminal_source_response base hb Θ g hk hcount
    (a := Gc) (b := Bc) (c := Cξ) (W := N) (V := 1) (Cr := Cr) (L := L) (D := Cl) (H := Hc) (ε := ε)
    hGc hBc hCξ.le (by dsimp only [N]; positivity) (by norm_num) hCr.le hL hCl hHc
    hε.le hεone hGhalf hBhalf
  dsimp only at hresponse
  have hactual := hresponse hg.1 hg.2.1 hg.2.2.1 hg.2.2.2 hbudget hFbound hpr.2.2 hmodels.1 hmodels.2.2.1
    hcurv hlineNorm hline hflags
  -- Restore the primitive source allowance after reconstructing the actual query.
  apply hactual.trans
  change Cc*ε^3≤((Cc+1)*Jn^3)*ω^3
  have heq : ((Cc+1)*Jn^3)*ω^3=(Cc+1)*ε^3 := by dsimp only [ε]; ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (by linarith : Cc≤Cc+1) (by positivity)

end
end krylov.Correction
