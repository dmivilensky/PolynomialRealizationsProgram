import krylov.Correction.RecordedAngle
import krylov.Correction.GatedStableStep
import krylov.Correction.ObservedAugmentedGram
import krylov.Correction.GatedCutoffAlgebra
import krylov.Correction.GatedPhaseGrowth

/-!
Article: main_krylov, thm:UCg, genuine uniform cutoff invariant.
Use: Construct and preserve actual recorded-prefix angle and quadratic
residual bounds with one set of constants chosen before the real run.
Source: proved genuine spectral-gated step, actual measured Gram/angle
identities, real projected-residual propagation and scalar cutoff algebra.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine old recorded-step nonzero, pair-angle and projected-gradient bounds used in the finite cutoff induction.
Use: Assemble the genuine uniform gated-RFC finite-cycle cutoff induction.
Article: main_krylov, thm:UCg, actual uniform cutoff invariant.
-/
def recordedPrefixBound {p : ℕ} (a C ε : ℝ) (s : Fin p → E) (g : E) : Prop :=
  (∀ i, s i≠0) ∧ (∀ i j, i≠j → |inner ℝ (unitWindow s i) (unitWindow s j)|≤a) ∧
    ‖projectedResidual (unitWindow s) g‖≤C*ε^2

/-- The actual empty observed prefix satisfies every finite angle and residual bound with a nonnegative allowance.
Use: Assemble the genuine uniform gated-RFC finite-cycle cutoff induction.
Article: main_krylov, thm:UCg, actual uniform cutoff invariant.
Proof: There are no old columns or angles, and the genuine zero-dimensional projected residual is zero.
-/
theorem recordedPrefixBound_empty (a C ε : ℝ) (hC : 0≤C) (g : E) :
    recordedPrefixBound a C ε (fun i : Fin 0 => Fin.elim0 i) g := by
  refine ⟨fun i => Fin.elim0 i,fun i => Fin.elim0 i,?_⟩
  have hz : projectedResidual (unitWindow (fun i : Fin 0 => Fin.elim0 i)) g=0 := Subsingleton.elim _ _
  rw [hz,norm_zero]
  positivity

/-- A genuine new recorded step preserves the full prefix property from its actual old/new angles and true next projected residual.
Use: Assemble the genuine uniform gated-RFC finite-cycle cutoff induction.
Article: main_krylov, thm:UCg, actual uniform cutoff invariant.
Proof: Keep the old nonzero vectors and pairings, add the real new nonzero step and its proved actual angles, then use the genuine next residual bound.
-/
theorem recordedPrefixBound_cons {p : ℕ} (a C ε : ℝ) (s : Fin p → E) (step g : E)
    (hs : ∀ i, s i≠0) (hstep : step≠0)
    (hold : ∀ i j, i≠j → |inner ℝ (unitWindow s i) (unitWindow s j)|≤a)
    (hnew : ∀ i, |inner ℝ (unitWindow s i) (NormedSpace.normalize step)|≤a)
    (hres : ‖projectedResidual (unitWindow (Fin.cons step s)) g‖≤C*ε^2) :
    recordedPrefixBound a C ε (Fin.cons step s) g := by
  refine ⟨fun i => Fin.cases hstep hs i,?_,hres⟩
  intro i j hij
  revert hij
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro hij; exact (hij rfl).elim
    · intro _hij
      change |inner ℝ (NormedSpace.normalize step) (unitWindow s j)|≤a
      rw [real_inner_comm]
      exact hnew j
  · refine Fin.cases ?_ (fun j => ?_) j
    · intro _hij
      change |inner ℝ (unitWindow s i) (NormedSpace.normalize step)|≤a
      exact hnew i
    · intro hij
      change |inner ℝ (unitWindow s i) (unitWindow s j)|≤a
      exact hold i j (fun h => hij (congrArg Fin.succ h))

/-- The explicit horizon-and-relative-correction coefficient in the genuine projected-residual recurrence.
Use: Assemble the genuine uniform gated-RFC finite-cycle cutoff induction.
Article: main_krylov, thm:UCg, actual uniform cutoff invariant.
-/
def gatedProjectedConstant (N : ℕ) (K : ℝ) : ℝ :=
  (2+K+(Real.sqrt (1/2))⁻¹*K)*((N : ℝ)*(2+K)*2)

/-- The actual uniform projected-residual coefficient is nonnegative for every finite horizon and nonnegative correction allowance.
Use: Assemble the genuine uniform gated-RFC finite-cycle cutoff induction.
Article: main_krylov, thm:UCg, actual uniform cutoff invariant.
Proof: All genuine dimension and square-root factors are nonnegative.
-/
theorem gatedProjectedConstant_nonneg (N : ℕ) {K : ℝ} (hK : 0≤K) :
    0≤gatedProjectedConstant N K := by unfold gatedProjectedConstant; positivity

/-- The true prefix projected-residual coefficient and search contribution are bounded by their common finite-horizon counterparts.
Use: Assemble the genuine uniform gated-RFC finite-cycle cutoff induction.
Article: main_krylov, thm:UCg, actual uniform cutoff invariant.
Proof: Increase only the genuine nonnegative dimension and square-root factors, preserving the actual residual and line magnitude.
-/
theorem projected_cutoff_uniform_bound {p N : ℕ} {ε K R t : ℝ}
    (hsize : p+1≤N) (hε : 0≤ε) (hK : 0≤K) (hR : 0≤R) (ht : 0≤t) :
    ((2+K+(Real.sqrt (1/2))⁻¹*K)*((p+1)*((2+K)*ε)*2))*
        (R+Real.sqrt (p+1)*(((2+K)*ε)*t))≤
      gatedProjectedConstant N K*ε*(R+(Real.sqrt N*(2+K))*ε*t) := by
  calc
    _ = gatedProjectedConstant (p+1) K*ε*(R+(Real.sqrt (p+1)*(2+K))*ε*t) := by
      unfold gatedProjectedConstant
      push_cast
      ring
    _ ≤ _ := by
      unfold gatedProjectedConstant
      gcongr
      exact_mod_cast hsize

/-- The actual spectral-gated step preserves the genuine recorded-prefix property above the quadratic line cutoff under one uniform set of quantitative allowances.
Use: Assemble the genuine uniform gated-RFC finite-cycle cutoff induction.
Article: main_krylov, thm:UCg, actual uniform cutoff invariant.
Proof: Actual image conjugacy and old recorded angles derive the real augmented Gram. Genuine common scalar margins prove both gates pass. The true old residual and large line derive the correction ratio, so the original measured step theorem gives real new angles and residual. Actual search growth and the proved scalar recurrence preserve the same quadratic allowance; no new trajectory bound is assumed.
-/
theorem recordedPrefixBound_gated_step {p N : ℕ} (s y : Fin p → E)
    (A B : E →L[ℝ] E) (g d : E) {a C M ε K γ L : ℝ}
    (hp : 0<p) (hN : 1≤N) (hsize : p+1≤N)
    (hγ : 0≤γ) (hγ1 : γ<1) (ha : 0<a) (ha1 : a<1) (hC : 0≤C) (hM : 0<M)
    (hε : 0<ε) (hK : 0≤K) (hg : ‖g‖≤L)
    (hprefix : recordedPrefixBound a C ε s g)
    (hA : ‖A-ContinuousLinearMap.id ℝ E‖≤ε) (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε)
    (hy : ∀ i, ‖y i-s i‖≤((1+K)*ε)*‖s i‖) (ho : ∀ i, inner ℝ (y i) d=0)
    (hc : inner ℝ d (A d)≠0)
    (hangle : (N : ℝ)*a≤(1-γ)/8) (hpair : (1+K)*ε≤a/2)
    (hratio : 4*C/M+4*(Real.sqrt N*(2+K))*ε≤a/4)
    (hsmall : gatedProjectedConstant N K*ε≤1/2)
    (hallow : 4*gatedProjectedConstant N K*(Real.sqrt N*(2+K))*L≤C)
    (hlarge : M*ε^2≤‖lineLength g d (A d) • d‖)
    (hrelative : ‖(gatedArrayPhase γ s y g d (A d) B).movement‖≤K*
      ‖lineLength g d (A d) • d+(gatedArrayPhase γ s y g d (A d) B).movement‖) :
    let P := gatedArrayPhase γ s y g d (A d) B
    let step := lineLength g d (A d) • d+P.movement
    recordedPrefixBound a C ε (Fin.cons step s) P.gradient := by
  let η := (1+K)*ε
  let line := lineLength g d (A d) • d
  let P := gatedArrayPhase γ s y g d (A d) B
  let step := line+P.movement
  have hη : 0≤η := by dsimp only [η]; positivity
  have hεη : ε≤η := by dsimp only [η]; nlinarith
  have hmargins := uniform_gate_margins hN hsize hγ hγ1 ha.le hη hpair hangle
  have hd : d≠0 := by intro hz; rw [hz,map_zero,inner_zero_left] at hc; exact hc rfl
  have hG := unit_augmented_observed_gram s y d hprefix.1 hd ha.le
    (show η≤a by linarith) hy ho hprefix.2.1
  have hdefect : (p : ℝ)*(4*η)<1 := by
    have ht : (p : ℝ)≤((p+1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ p
    exact (mul_le_mul_of_nonneg_right ht (by positivity)).trans_lt hmargins.2.2.2
  have hline : 0<‖line‖ := lt_of_lt_of_le (mul_pos hM (sq_pos_of_pos hε)) hlarge
  have hcut := large_line_residual_ratio hC hM hprefix.2.2 hlarge hratio
  have hcut' : 4*(‖projectedResidual (unitWindow s) g‖+Real.sqrt N*(((2+K)*ε)*‖line‖))≤a/4*‖line‖ := by
    simpa only [mul_assoc] using hcut
  have hq : a/4<1 := by linarith
  have hstep := gated_stable_recorded_step s y hprefix.1 A B g d hp hsize hε.le hK hγ hq hA hB hy ho hc
    hG hmargins.1 hmargins.2.1 hmargins.2.2.1 hdefect hline hcut' hrelative
  have hlinebound : ‖line‖≤2*L :=
    (actual_line_norm_bound A g d hA (hεη.trans hmargins.1)).trans (mul_le_mul_of_nonneg_left hg (by norm_num : (0 : ℝ)≤2))
  have hres := hstep.2.2.2.trans (projected_cutoff_uniform_bound hsize hε.le hK
    (norm_nonneg (projectedResidual (unitWindow s) g)) (norm_nonneg line))
  have hnext : ‖projectedResidual (unitWindow (Fin.cons step s)) P.gradient‖≤C*ε^2 :=
    hres.trans (quadratic_residual_invariant hε.le hC (gatedProjectedConstant_nonneg N hK)
      (by positivity : 0≤Real.sqrt N*(2+K)) hprefix.2.2 hlinebound hsmall hallow)
  apply recordedPrefixBound_cons a C ε s step P.gradient hprefix.1 hstep.2.1 hprefix.2.1 ?_ hnext
  intro i
  exact (hstep.2.2.1 i).trans (by linarith)

end
end krylov.Correction
