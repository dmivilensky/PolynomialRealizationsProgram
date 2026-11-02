import krylov.Nonlinear.RFCSSelfConcordantFunction
import krylov.Nonlinear.RFCSStationary

/-!
Article: main_krylov, thm:RFCS, actual restarted self-concordant cycle consequence.
Use: Run the genuine scalar-gradient RFC-S executor with fresh full memory
at each actual restart and derive the printed uniform eventual metric-error
inequality before compact full-active normalized cycle directions.
Source: the proved actual scalar-function single-cycle theorem, genuine CG
cycle-reference quantities, real convergence and exact stationary execution.
The finite probe extension removes assumptions about values never queried.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Filter Topology Metric krylov.Methods krylov.Reference InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact finite-cycle probe sequence extended by one beyond the real queried horizon.
Use: Use only the original finite probe data without imposing any extra nonzero-oracle condition outside the executed cycle.
Article: main_krylov, thm:RFCS, genuine restarted scalar-function cycles.
-/
def rfcSCycleProbe (N : ℕ) (h : ℕ → ℝ) (i : ℕ) : ℝ := if i<N then h i else 1

/-- The true restarted nonlinear RFC-S points obtained by executing a fresh genuine full-memory cycle at every restart.
Use: Tie the asymptotic cycle-error conclusion to the actual recursively executed scalar-gradient method.
Article: main_krylov, thm:RFCS, genuine restarted scalar-function cycles.
-/
def rfcSRestartedPoints (G : E → E) (N : ℕ) (h : ℕ → ℕ → ℝ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | c+1 => rfcSFunctionPoint fullMemory G (rfcSRestartedPoints G N h x₀ c) (rfcSCycleProbe N (h c)) N

variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- Actual restarted RFC-S on a standard self-concordant scalar function satisfies the printed eventual cycle-error inequality with its actual last relative probe error, true quadratic-reference penultimate error and one uniform cubic remainder, including exact stationary tails.
Use: Close the original restarted scalar-function consequence under the source compact nondegeneracy, bounded-probe and convergence assumptions.
Article: main_krylov, thm:RFCS, genuine restarted scalar-function cycles.
Proof: Construct the compact genuine initial-gradient reference family from actual normalized cycle directions. The true metric inverse bounds those physical directions uniformly. Convergence places every sufficiently late active cycle in the proved common single-cycle neighborhood. Exact metric scaling identifies its actual initial point and original CG reference error. The actual stationary-run theorem handles zero-error cycles, and a finite probe extension supplies only unqueried dummy values.
-/
theorem restarted_rfcs_selfConcordant_function (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (hk : 0<k) (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ) (r Cp : ℝ) (hr : 0<r) (hCp : 0<Cp)
    (hsc : IsStandardSelfConcordantOn f (ball 0 r)) (h₀ : gradient f 0=0)
    (hH₀ : fderiv ℝ (gradient f) 0=cgOperator base)
    (U : Set (EuclideanSpace ℝ (Fin (k+1)))) (hU : IsCompact U)
    (hactive : ∀ u∈U, k+1≤referenceAtomCount base hb (cgOperator base u))
    (h : ℕ → ℕ → ℝ) (x₀ : EuclideanSpace ℝ (Fin (k+1))) :
    let T := metricCoordinates base hb
    let x := rfcSRestartedPoints (gradient f) (k+1) h x₀
    let e := fun c => ‖T (x c)‖
    let u := fun c => (e c)⁻¹ • x c
    (∀ c, 0<e c → u c∈U) → Tendsto e atTop (𝓝 0) →
    (∀ c, 0<e c → ∀ i<k+1, 0<h c i ∧ h c i≤Cp*CG.length (cgOperator base) (cgOperator base (x c)) i) →
    ∃ C : ℝ, 0<C ∧ ∀ᶠ c in atTop,
      e (c+1)≤|1-h c k/rfcSFunctionAlpha fullMemory (gradient f) (x c) (rfcSCycleProbe (k+1) (h c)) k| *
        ‖cgCanonicalError base (cgOperator base (x c)) k‖^2+C*(e c)^3 := by
  let T := metricCoordinates base hb
  let x := rfcSRestartedPoints (gradient f) (k+1) h x₀
  let e := fun c => ‖T (x c)‖
  let u := fun c => (e c)⁻¹ • x c
  dsimp only
  intro hdirs hconv hprobes
  let K := cgOperator base '' U
  have hK : IsCompact K := hU.image (cgOperator base).continuous
  have hKactive g (hg : g∈K) : k+1≤referenceAtomCount base hb g := by
    obtain ⟨v,hv,rfl⟩ := hg
    exact hactive v hv
  let B := ‖T.symm.toContinuousLinearMap‖+1
  have hB : 0<B := by dsimp only [B]; positivity
  obtain ⟨ε₀,C,hε₀,hC,hcycle⟩ := compact_rfcs_selfConcordant_function base hb K hK hKactive hk f r B Cp hr hB hCp hsc h₀ hH₀
  refine ⟨C,hC,?_⟩
  have hevent : ∀ᶠ c in atTop, e c<ε₀ := hconv.eventually (gt_mem_nhds hε₀)
  filter_upwards [hevent] with c hc
  change e (c+1)≤|1-h c k/rfcSFunctionAlpha fullMemory (gradient f) (x c) (rfcSCycleProbe (k+1) (h c)) k| *
    ‖cgCanonicalError base (cgOperator base (x c)) k‖^2+C*(e c)^3
  -- Active cycles use the proved genuine scalar-function estimate; stationary cycles retain their exact zero error.
  by_cases he : 0<e c
  · have hdecomp : e c • u c=x c := by
      change e c • ((e c)⁻¹ • x c)=x c
      rw [smul_smul,mul_inv_cancel₀ he.ne',one_smul]
    have hunit : ‖T (u c)‖=1 := by
      change ‖T ((e c)⁻¹ • x c)‖=1
      rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr he.le)]
      change (e c)⁻¹*(e c)=1
      exact inv_mul_cancel₀ he.ne'
    have hu : ‖u c‖≤B := by
      have hn := T.symm.toContinuousLinearMap.le_opNorm (T (u c))
      simp only [ContinuousLinearEquiv.coe_coe,T.symm_apply_apply,hunit,mul_one] at hn
      exact hn.trans (by dsimp only [B]; linarith)
    have hKu : cgOperator base (u c)∈K := ⟨u c,hdirs c he,rfl⟩
    have hnonzero i : rfcSCycleProbe (k+1) (h c) i≠0 := by
      by_cases hi : i<k+1
      · rw [rfcSCycleProbe,ite_eq_left hi]
        exact (hprobes c he i hi).1.ne'
      · rw [rfcSCycleProbe,ite_eq_right hi]
        norm_num
    have hrel i (hi : i<k+1) : 0<rfcSCycleProbe (k+1) (h c) i ∧
        rfcSCycleProbe (k+1) (h c) i≤Cp*CG.length (cgOperator base) (cgOperator base (e c • u c)) i := by
      rw [hdecomp,rfcSCycleProbe,ite_eq_left hi]
      exact hprobes c he i hi
    have hout := hcycle (e c) he hc (u c) hu hKu (rfcSCycleProbe (k+1) (h c)) hnonzero hrel
    rw [hdecomp] at hout
    have hlast : rfcSCycleProbe (k+1) (h c) k=h c k := by rw [rfcSCycleProbe,ite_eq_left (Nat.lt_succ_self k)]
    rw [hlast] at hout
    exact hout
  · have he₀ : e c=0 := le_antisymm (by linarith) (norm_nonneg (T (x c)))
    have hx : x c=0 := by
      apply T.injective
      simpa only [map_zero] using norm_eq_zero.mp he₀
    have hnext : e (c+1)=0 := by
      change ‖T (rfcSFunctionPoint fullMemory (gradient f) (x c) (rfcSCycleProbe (k+1) (h c)) (k+1))‖=0
      rw [hx,rfcSFunctionPoint_stationary fullMemory (gradient f) 0 _ h₀ (k+1),map_zero,norm_zero]
    rw [hnext,he₀]
    positivity

end
end krylov.Nonlinear
