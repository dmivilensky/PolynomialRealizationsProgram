import krylov.XR.LocalParametricVirtual
import krylov.XR.LocalTrialComparison

/-!
Article: main_krylov, lem:xr-local, genuine prescribed-trial comparison.
Use: execute XRFC with a literal finite vector of trial scalars, prove its
joint C² dependence on actual segment operators and those scalars, and
derive quadratic trial independence from the genuine executed CG flag.
The resulting O(||E||²) comparison has no assumed output jet or trajectory.
Source: actual parametric finite solves, true quadratic XRFC independence,
and the proved mixed-derivative mean-value estimate.
-/

namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology Asymptotics
open krylov.Methods krylov.Reference krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual data-only rule selecting the next prescribed scalar by
the number of genuinely observed gradient records. -/
def prescribedTrial {N : ℕ} (tau : Fin N → ℝ) (H : History E) : ℝ :=
  if h : H.records.length < N then tau ⟨H.records.length, h⟩ else 1

omit [CompleteSpace E] in
/-- The k-th actual query uses exactly the k-th prescribed scalar;
the oracle and the executed policy do not supply this equality as a field. -/
theorem prescribedTrial_run_scalar {N : ℕ} (tau : Fin N → ℝ) (m : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (hk : k < N) :
    prescribedTrial tau (oneGradientRun m A g k) = tau ⟨k, hk⟩ := by
  unfold prescribedTrial
  rw [oneGradientRun_length, dite_eq_left hk]

/-- Actual segment-operator inputs, with one extra coordinate reserved
for the semantic operator at the unevaluated output. -/
def prescribedOperatorPath {N : ℕ} (Q : E →L[ℝ] E) (errors : Fin (N + 1) → E →L[ℝ] E)
    (k : ℕ) : E →L[ℝ] E :=
  if h : k < N then Q + errors ⟨k, by omega⟩ else Q

/-- True physical output point and semantic output gradient of the actual
prescribed-trial XRFC executor. Its terminal correction makes no query. -/
def prescribedXRFCOutput (Q : E →L[ℝ] E) (g : E) (N : ℕ)
    (z : (Fin (N + 1) → E →L[ℝ] E) × (Fin N → ℝ)) : E × E :=
  let m := xrfcMethod fullMemory (prescribedTrial z.2)
  let H := oneGradientRun m (prescribedOperatorPath Q z.1) g N
  (m.outputDisplacement H, m.outputGradient (Q + z.1 (Fin.last N)) H)

omit [CompleteSpace E] in
theorem prescribedOperatorPath_zero (Q : E →L[ℝ] E) (N : ℕ) :
    prescribedOperatorPath Q (0 : Fin (N + 1) → E →L[ℝ] E) = fun _ => Q := by
  funext k
  unfold prescribedOperatorPath
  split_ifs <;> simp only [Pi.zero_apply, add_zero]

/-- Actual prescribed-trial XRFC has genuine joint C² outputs near every
true nonstagnating positive quadratic and every nonzero trial vector. -/
theorem prescribedXRFCOutput_contDiffAt (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i < N, CG.gradient Q g i ≠ 0)
    (tau₀ : Fin N → ℝ) (htau : ∀ i, tau₀ i ≠ 0) :
    ContDiffAt ℝ 2 (prescribedXRFCOutput Q g N) (0, tau₀) := by
  let Z := (Fin (N + 1) → E →L[ℝ] E) × (Fin N → ℝ)
  let x : Z := (0, tau₀)
  let trial := fun z : Z => prescribedTrial (E := E) z.2
  let A := fun z : Z => prescribedOperatorPath Q z.1
  let m := fun z : Z => xrfcMethod fullMemory (trial z)
  have herror (i : Fin (N + 1)) : ContDiffAt ℝ 2 (fun z : Z => z.1 i) x :=
    (contDiffAt_pi.mp (contDiffAt_fst : ContDiffAt ℝ 2 (fun z : Z => z.1) x)) i
  have htcoord (i : Fin N) : ContDiffAt ℝ 2 (fun z : Z => z.2 i) x :=
    (contDiffAt_pi.mp (contDiffAt_snd : ContDiffAt ℝ 2 (fun z : Z => z.2) x)) i
  have hA (k : ℕ) : ContDiffAt ℝ 2 (fun z => A z k) x := by
    unfold A prescribedOperatorPath
    split_ifs with hk
    · exact contDiffAt_const.add (herror ⟨k, by omega⟩)
    · exact contDiffAt_const
  have hAz : A x = fun _ => Q := prescribedOperatorPath_zero Q N
  have ht (i : ℕ) (hi : i < N) : prescribedTrial tau₀
      (oneGradientRun (xrfcMethod fullMemory (prescribedTrial tau₀)) (fun _ => Q) g i) ≠ 0 := by
    rw [prescribedTrial_run_scalar _ _ _ _ i hi]
    exact htau ⟨i, hi⟩
  have hd (k : ℕ) (hk : k ≤ N) := xrfc_full_array_domains (prescribedTrial tau₀) Q hQ hpos g N hpre ht k hk
  have hM (k : ℕ) (hk : k < N) : (pairModel
      (fun i : Fin k => oneGradientStep (m x) (A x) g (k - 1 - i.val))
      (fun i : Fin k => A x (k - 1 - i.val) (oneGradientStep (m x) (A x) g (k - 1 - i.val)))).det ≠ 0 := by
    rw [hAz]
    exact (hd k hk.le).2
  have hY (k : ℕ) (hk : k < N) : (crossGram
      (fun i : Fin k => A x (k - 1 - i.val) (oneGradientStep (m x) (A x) g (k - 1 - i.val)))
      (fun i : Fin k => oneGradientStep (m x) (A x) g (k - 1 - i.val))).det ≠ 0 := by
    rw [hAz]
    exact (hd k hk.le).1
  have htrial (k : ℕ) (hk : k < N) : ContDiffAt ℝ 2
      (fun z => trial z (oneGradientRun (m z) (A z) g k)) x := by
    exact (htcoord ⟨k, hk⟩).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z =>
      prescribedTrial_run_scalar z.2 (m z) (A z) g k hk)
  have hp := parametric_xrfc_prefix_contDiffAt trial A (fun _ => g) x N
    (fun i _ => hA i) contDiffAt_const hM hY htrial
  have hv := parametric_oneGradient_virtual_contDiffAt m A (fun _ => g) x N
    (fun i _ => hA i) hp.2 (hp.1 N le_rfl)
    (by rw [hAz]; exact (hd N le_rfl).2) (by rw [hAz]; exact (hd N le_rfl).1)
  have hdisp : ContDiffAt ℝ 2 (fun z => (oneGradientRun (m z) (A z) g N).displacement) x := by
    simp only [oneGradientRun_displacement_sum]
    exact ContDiffAt.sum (fun i hi => hp.2 i (Finset.mem_range.mp hi))
  have hB : ContDiffAt ℝ 2 (fun z : Z => Q + z.1 (Fin.last N)) x :=
    contDiffAt_const.add (herror (Fin.last N))
  exact (hdisp.add hv.1).prodMk ((hp.1 N le_rfl).add (hB.clm_apply hv.1))

omit [CompleteSpace E] in
/-- The actual prescribed-trial quadratic output is independent of every
nonzero trial, for both its physical point and semantic gradient. -/
theorem prescribedXRFCOutput_zero (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i < N, CG.gradient Q g i ≠ 0)
    (tau : Fin N → ℝ) (htau : ∀ i, tau i ≠ 0) :
    prescribedXRFCOutput Q g N (0, tau) = (CG.displacement Q g N, CG.gradient Q g N) := by
  let m := xrfcMethod fullMemory (prescribedTrial tau) (E := E)
  let H := oneGradientRun m (fun _ => Q) g N
  have ht (i : ℕ) (hi : i < N) : prescribedTrial tau (oneGradientRun m (fun _ => Q) g i) ≠ 0 := by
    rw [prescribedTrial_run_scalar _ _ _ _ i hi]
    exact htau ⟨i, hi⟩
  have href := xrfc_full_reference (prescribedTrial tau) Q hQ hpos g N hpre ht N le_rfl
  have hgradient : m.outputGradient Q H = CG.gradient Q g N := by
    unfold OneGradientMethod.outputGradient
    rw [oneGradientRun_quadratic_gradient]
    rw [add_assoc, ← map_add]
    change g + Q (m.outputDisplacement H) = _
    rw [href.1, ← CG.gradient_displacement]
  simp only [prescribedXRFCOutput, prescribedOperatorPath_zero, Pi.zero_apply, add_zero]
  exact Prod.ext href.1 hgradient

/-- The original second-order trial comparison for the actual operator-
sequence XRFC output. Joint C² regularity and reference trial independence
are proved above, not supplied as output or jet hypotheses. -/
theorem prescribedXRFC_trial_comparison (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ i < N, CG.gradient Q g i ≠ 0)
    (tau₀ : Fin N → ℝ) (htau : ∀ i, tau₀ i ≠ 0)
    (tau₁ tau₂ : (Fin (N + 1) → E →L[ℝ] E) → Fin N → ℝ)
    (h₁ : Tendsto tau₁ (𝓝 0) (𝓝 tau₀)) (h₂ : Tendsto tau₂ (𝓝 0) (𝓝 tau₀))
    (hdiff : (fun e => tau₂ e - tau₁ e) =O[𝓝 0] (fun e : Fin (N + 1) → E →L[ℝ] E => ‖e‖)) :
    (fun e => prescribedXRFCOutput Q g N (e, tau₂ e) - prescribedXRFCOutput Q g N (e, tau₁ e))
      =O[𝓝 0] (fun e : Fin (N + 1) → E →L[ℝ] E => ‖e‖ ^ 2) := by
  have hnonzero : ∀ᶠ tau in 𝓝 tau₀, ∀ i, tau i ≠ 0 :=
    Filter.eventually_all.mpr (fun i =>
      (continuous_apply i).continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds (htau i)))
  have hzero : ∀ᶠ tau in 𝓝 tau₀,
      prescribedXRFCOutput Q g N (0, tau) = prescribedXRFCOutput Q g N (0, tau₀) := by
    filter_upwards [hnonzero] with tau ht
    rw [prescribedXRFCOutput_zero Q hQ hpos g N hpre tau ht,
      prescribedXRFCOutput_zero Q hQ hpos g N hpre tau₀ htau]
  exact c2_reference_trial_comparison_bigO (prescribedXRFCOutput Q g N) tau₀
    (prescribedXRFCOutput_contDiffAt Q hQ hpos g N hpre tau₀ htau) hzero tau₁ tau₂ h₁ h₂ hdiff

end
end krylov.XR
