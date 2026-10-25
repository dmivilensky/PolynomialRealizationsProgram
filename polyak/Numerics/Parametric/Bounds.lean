import polyak.Numerics.Parametric.Dyadic

/-! Article: Appendix B, source-linked scalar reserves on parameter boxes. -/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def boundCheck {n : ℕ} (e : Expr) (I : IntervalRat) (X : Fin n → IntervalRat)
    (cfg : DyadicConfig) (strict : Bool) : Bool :=
  decide (cfg.precision≤0) && succeeded (dyadicValue e (finBoxEnv (box I X)) cfg) &&
    (if strict then decide (0<(outcome (dyadicValue e (finBoxEnv (box I X)) cfg)).lo)
     else decide (0≤(outcome (dyadicValue e (finBoxEnv (box I X)) cfg)).lo))

noncomputable section

theorem boundCheck_sound {n : ℕ} (e : Expr) (I : IntervalRat)
    (X : Fin n → IntervalRat) (cfg : DyadicConfig) (strict : Bool)
    (hc : boundCheck e I X cfg strict=true) {s : ℝ} {x : Fin n → ℝ}
    (hs : s∈I) (hx : FinBoxMem x X) :
    if strict then 0<eval e s x else 0≤eval e s x := by
  simp only [boundCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  have hm := dyadicValue_mem e (finBoxEnv (box I X)) cfg hc.1.1
    (finEnv (embed s x)) (finEnv_mem_finBoxEnv (embed_mem_box hs hx)) hc.1.2
  have hlo := hm.1
  cases strict
  · simp only [Bool.false_eq_true, ↓reduceIte,decide_eq_true_eq] at hc ⊢
    have hb : (0 : ℝ)≤(outcome (dyadicValue e (finBoxEnv (box I X)) cfg)).lo := by
      exact_mod_cast hc.2
    exact hb.trans hlo
  · simp only [↓reduceIte,decide_eq_true_eq] at hc ⊢
    have hb : (0 : ℝ)<(outcome (dyadicValue e (finBoxEnv (box I X)) cfg)).lo := by
      exact_mod_cast hc.2
    exact hb.trans_le hlo

end
end polyak.Numerics.Parametric
