import polyak.Numerics.Parametric.Gluing
import polyak.Numerics.Parametric.Invertible

/-!
Article: Appendix B, analytic implicit roots on checked continuation slabs.
Use: interval contractions prove the actual unknown derivative is invertible.
The analytic implicit function theorem therefore applies to the source system.
-/
noncomputable section
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine Filter
open scoped Topology ContDiff

theorem eval_contDiff {n : ℕ} (e : Expr) (he : ADSupported e) :
    ContDiff ℝ ω (fun p : ℝ×(Fin n → ℝ) => eval e p.1 p.2) := by
  induction he with
  | const q => exact contDiff_const
  | var i =>
    cases i with
    | zero =>
      simpa [eval,evalFin,finEnv,embed] using
        (contDiff_fst : ContDiff ℝ ω (Prod.fst : ℝ×(Fin n → ℝ) → ℝ))
    | succ j =>
      simp only [eval,evalFin,Expr.eval_var,finEnv_embed_succ]
      by_cases hj : j<n
      · simp only [dite_eq_left hj]
        have hp : ContDiff ℝ ω (fun x : Fin n → ℝ => x ⟨j,hj⟩) :=
          (ContinuousLinearMap.proj (⟨j,hj⟩ : Fin n) : (Fin n → ℝ) →L[ℝ] ℝ).contDiff
        exact hp.comp contDiff_snd
      · simp only [dite_eq_right hj]
        exact contDiff_const
  | add _ _ ha hb => exact ha.add hb
  | mul _ _ ha hb => exact ha.mul hb
  | neg _ ha => exact ha.neg
  | exp _ ha => exact Real.contDiff_exp.comp ha
  | sin _ ha => exact Real.contDiff_sin.comp ha
  | cos _ ha => exact Real.contDiff_cos.comp ha

def joint {n : ℕ} (F : Fin n → Expr) (p : ℝ×(Fin n → ℝ)) : Fin n → ℝ := system F p.1 p.2

theorem joint_contDiff {n : ℕ} (F : Fin n → Expr) (hF : ∀ i, ADSupported (F i)) :
    ContDiff ℝ ω (joint F) := contDiff_pi.mpr (fun i => eval_contDiff (F i) (hF i))

theorem joint_partial {n : ℕ} (F : Fin n → Expr) (hF : ∀ i, ADSupported (F i))
    (s : ℝ) (x : Fin n → ℝ) :
    fderiv ℝ (joint F) (s,x) ∘L ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)=
      fderiv ℝ (system F s) x := by
  have hi : HasFDerivAt (fun y : Fin n → ℝ => (s,y))
      (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)) x :=
    (hasFDerivAt_const (𝕜 := ℝ) (c := s) (x := x)).prodMk (hasFDerivAt_id x)
  have hc := ((joint_contDiff F hF).differentiable (by simp)).differentiableAt.hasFDerivAt.comp x hi
  exact hc.unique (system_differentiable F hF s x).hasFDerivAt

theorem check_analytic_branch {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (X : Fin n → IntervalRat) (cert : Certificate n) (cfg : EvalConfig)
    (hc : check F I X cert cfg=true) {s : ℝ} {x : Fin n → ℝ}
    (hs : s∈I) (hx : FinBoxMem x X) (hz : system F s x=0) :
    ∃ g : ℝ → (Fin n → ℝ), AnalyticAt ℝ g s ∧ g s=x ∧
      (∀ᶠ t in 𝓝 s, system F t (g t)=0) ∧
      ∀ᶠ p in 𝓝 (s,x), system F p.1 p.2=0 ↔ g p.1=p.2 := by
  have hdata := hc
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hdata
  have hF : ∀ i, ADSupported (F i) :=
    fun i => ((F i).checkADSupported_eq_true_iff).mp (hdata.1.1.1.1 i)
  have hcd := (joint_contDiff F hF).contDiffAt (x := (s,x))
  have hi : (fderiv ℝ (joint F) (s,x) ∘L
      ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)).IsInvertible := by
    rw [joint_partial F hF]
    exact check_derivative_isInvertible F I X cert cfg hc hs hx
  let g := hcd.implicitFunction (by simp) hi
  refine ⟨g,(hcd.contDiffAt_implicitFunction (by simp) hi).analyticAt,
    hcd.implicitFunction_apply_self (by simp) hi,?_,?_⟩
  · simpa only [joint,hz,g] using hcd.eventually_apply_implicitFunction (by simp) hi
  · simpa only [joint,hz,g] using hcd.eventually_apply_eq_iff_implicitFunction (by simp) hi

end polyak.Numerics.Parametric
