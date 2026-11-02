import krylov.Correction.GatedCutoffInvariant

/-!
Article: main_krylov, thm:UCq, linear normalized-angle propagation.
Use: Strengthen the genuine quadratic-cutoff prefix invariant to angles of
order omega when the actual current line is at least the variation scale.
Source: proved real gate acceptance, actual correction noncancellation,
observed pair conjugacy and the original projected-residual recurrence.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The explicit correction-to-line coefficient derived from the true quadratic old residual and finite search contribution.
Use: Choose actual uniform RFC constants before every reference and source scenario.
Article: main_krylov, thm:UCq.
-/
def rfcRelativeCorrectionConstant (N : ℕ) (K C : ℝ) : ℝ :=
  4*C+4*(Real.sqrt N*(2+K))

/-- The explicit linear-angle allowance includes both real pair error and actual correction-induced rotation.
Use: Choose actual uniform RFC constants before every reference and source scenario.
Article: main_krylov, thm:UCq.
-/
def rfcLinearAngleConstant (N : ℕ) (K C : ℝ) : ℝ :=
  2*(1+K)+2*rfcRelativeCorrectionConstant N K C

/-- A true relative-to-line old projected residual propagates actual linear angles and quadratic residuals without a lower line-length cutoff.
Use: Handle the genuine small intermediate step in the three-dimensional exception.
Article: main_krylov, thm:UCq.
Proof: Actual observed conjugacy and scalar margins derive both real gate tests and the augmented Gram. The supplied genuine old-residual-to-line bound directly controls the actual correction ratio. The existing recorded-step and projected-residual identities close the same true invariant. Only strict positivity of the actual line is needed.
-/
theorem recordedPrefixBound_linear_step_of_relative_residual {p N : ℕ} (s y : Fin p → E)
    (A B : E →L[ℝ] E) (g d : E) {C ε K γ L : ℝ}
    (hp : 0<p) (hN : 1≤N) (hsize : p+1≤N)
    (hγ : 0≤γ) (hγ1 : γ<1) (hC : 0≤C) (hε : 0<ε) (hK : 0≤K) (hg : ‖g‖≤L)
    (hprefix : recordedPrefixBound (rfcLinearAngleConstant N K C*ε) C ε s g)
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤ε) (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε)
    (hy : ∀ i, ‖y i-s i‖≤((1+K)*ε)*‖s i‖) (ho : ∀ i, inner ℝ (y i) d=0)
    (hc : inner ℝ d (A d)≠0)
    (hangle : (N : ℝ)*(rfcLinearAngleConstant N K C*ε)≤(1-γ)/8)
    (hsmall : gatedProjectedConstant N K*ε≤1/2)
    (hallow : 4*gatedProjectedConstant N K*(Real.sqrt N*(2+K))*L≤C)
    (hline : 0<‖lineLength g d (A d) • d‖)
    (hRrelative : ‖projectedResidual (unitWindow s) g‖≤C*ε*‖lineLength g d (A d) • d‖)
    (hrelative : ‖(gatedArrayPhase γ s y g d (A d) B).movement‖≤K*
      ‖lineLength g d (A d) • d+(gatedArrayPhase γ s y g d (A d) B).movement‖) :
    let P := gatedArrayPhase γ s y g d (A d) B
    let step := lineLength g d (A d) • d+P.movement
    recordedPrefixBound (rfcLinearAngleConstant N K C*ε) C ε (Fin.cons step s) P.gradient ∧
      ‖P.movement‖≤(rfcRelativeCorrectionConstant N K C*ε)*‖lineLength g d (A d) • d‖ := by
  let a := rfcLinearAngleConstant N K C
  let Q := rfcRelativeCorrectionConstant N K C
  let η := (1+K)*ε
  let line := lineLength g d (A d) • d
  let P := gatedArrayPhase γ s y g d (A d) B
  have hQ : 0≤Q := by dsimp only [Q,rfcRelativeCorrectionConstant]; positivity
  have ha : 0<a := by dsimp only [a,rfcLinearAngleConstant]; change 0<2*(1+K)+2*Q; positivity
  have hη : 0≤η := by dsimp only [η]; positivity
  have hηa : η≤(a*ε)/2 := by dsimp only [η,a,rfcLinearAngleConstant]; change (1+K)*ε≤(2*(1+K)+2*Q)*ε/2; nlinarith
  have hm := uniform_gate_margins hN hsize hγ hγ1 (mul_nonneg ha.le hε.le) hη hηa hangle
  have hd : d≠0 := by intro hz; rw [hz,map_zero,inner_zero_left] at hc; exact hc rfl
  have hG := unit_augmented_observed_gram s y d hprefix.1 hd (mul_nonneg ha.le hε.le)
    (show η≤a*ε by linarith) hy ho hprefix.2.1
  have hdefect : (p : ℝ)*(4*η)<1 := by
    have hp' : (p : ℝ)≤((p+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ p
    exact (mul_le_mul_of_nonneg_right hp' (by positivity)).trans_lt hm.2.2.2
  have hN' : (1 : ℝ)≤N := by exact_mod_cast hN
  have hscale : a*ε≤(N : ℝ)*(a*ε) := by nlinarith [mul_nonneg ha.le hε.le]
  have haε : a*ε≤(1-γ)/8 := hscale.trans hangle
  have hq : Q*ε<1 := by
    have hqa : 2*Q≤a := by dsimp only [a,rfcLinearAngleConstant]; change 2*Q≤2*(1+K)+2*Q; linarith
    have ht := mul_le_mul_of_nonneg_right hqa hε.le
    nlinarith
  have hcut : 4*(‖projectedResidual (unitWindow s) g‖+
      Real.sqrt N*(((2+K)*ε)*‖line‖))≤(Q*ε)*‖line‖ := by
    have hr := hRrelative
    dsimp only [Q,rfcRelativeCorrectionConstant]
    nlinarith
  have hs := gated_stable_recorded_step s y hprefix.1 A B g d hp hsize hε.le hK hγ hq hA hB hy ho hc
    hG hm.1 hm.2.1 hm.2.2.1 hdefect hline hcut hrelative
  have hhalf : ε≤1/2 := by
    have ht : ε≤η := by dsimp only [η]; nlinarith
    exact ht.trans hm.1
  have hlinebound : ‖line‖≤2*L := (actual_line_norm_bound A g d hA hhalf).trans
    (mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ)≤2))
  have hres := hs.2.2.2.trans (projected_cutoff_uniform_bound hsize hε.le hK
    (norm_nonneg (projectedResidual (unitWindow s) g)) (norm_nonneg line))
  have hnext : ‖projectedResidual (unitWindow (Fin.cons (line+P.movement) s)) P.gradient‖≤C*ε^2 :=
    hres.trans (quadratic_residual_invariant hε.le hC (gatedProjectedConstant_nonneg N hK)
      (by positivity : 0≤Real.sqrt N*(2+K)) hprefix.2.2 hlinebound hsmall hallow)
  dsimp only
  refine ⟨recordedPrefixBound_cons (a*ε) C ε s (line+P.movement) P.gradient hprefix.1 hs.2.1
    hprefix.2.1 (fun i => (hs.2.2.1 i).trans ?_) hnext,hs.1⟩
  dsimp only [a,rfcLinearAngleConstant]
  change (1+K)*ε+2*(Q*ε)≤(2*(1+K)+2*Q)*ε
  nlinarith



/-- The actual gated correction preserves a linear-in-budget old-angle bound and a quadratic true projected-gradient bound whenever its actual line exceeds the variation scale.
Use: Close ordinary-RFC normalized-model conditioning under the genuine nonstagnation condition.
Article: main_krylov, thm:UCq.
Proof: The actual observed old angles and image conjugacy derive the real augmented Gram. Common scalar margins force both original tests to pass. The true line lower bound converts the quadratic old residual to a linear relative-correction estimate, proving noncancellation and new linear angles. The original measured projected-residual recurrence preserves the same quadratic allowance.
-/
theorem recordedPrefixBound_linear_step {p N : ℕ} (s y : Fin p → E)
    (A B : E →L[ℝ] E) (g d : E) {C ε K γ L : ℝ}
    (hp : 0<p) (hN : 1≤N) (hsize : p+1≤N)
    (hγ : 0≤γ) (hγ1 : γ<1) (hC : 0≤C) (hε : 0<ε) (hK : 0≤K) (hg : ‖g‖≤L)
    (hprefix : recordedPrefixBound (rfcLinearAngleConstant N K C*ε) C ε s g)
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤ε) (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε)
    (hy : ∀ i, ‖y i-s i‖≤((1+K)*ε)*‖s i‖) (ho : ∀ i, inner ℝ (y i) d=0)
    (hc : inner ℝ d (A d)≠0)
    (hangle : (N : ℝ)*(rfcLinearAngleConstant N K C*ε)≤(1-γ)/8)
    (hsmall : gatedProjectedConstant N K*ε≤1/2)
    (hallow : 4*gatedProjectedConstant N K*(Real.sqrt N*(2+K))*L≤C)
    (hlarge : ε≤‖lineLength g d (A d) • d‖)
    (hrelative : ‖(gatedArrayPhase γ s y g d (A d) B).movement‖≤K*
      ‖lineLength g d (A d) • d+(gatedArrayPhase γ s y g d (A d) B).movement‖) :
    let P := gatedArrayPhase γ s y g d (A d) B
    let step := lineLength g d (A d) • d+P.movement
    recordedPrefixBound (rfcLinearAngleConstant N K C*ε) C ε (Fin.cons step s) P.gradient ∧
      ‖P.movement‖≤(rfcRelativeCorrectionConstant N K C*ε)*‖lineLength g d (A d) • d‖ := by
  have hRrelative : ‖projectedResidual (unitWindow s) g‖≤C*ε*‖lineLength g d (A d) • d‖ := by
    have ht := mul_le_mul_of_nonneg_left hlarge (mul_nonneg hC hε.le)
    have hprod : C*ε^2≤C*ε*‖lineLength g d (A d) • d‖ := by nlinarith only [ht]
    exact hprefix.2.2.trans hprod
  exact recordedPrefixBound_linear_step_of_relative_residual s y A B g d
    hp hN hsize hγ hγ1 hC hε hK hg hprefix hA hB hy ho hc hangle hsmall hallow
    (hε.trans_le hlarge) hRrelative hrelative

end
end krylov.Correction
