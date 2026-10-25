import polyak.Numerics.Parametric.DerivativeTwo

/-! Checked literal enclosures for source derivatives. Arithmetic certificates
can reuse these finite matrices without unfolding the AD evaluator repeatedly. -/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def derivativeEntryCheck (e : Expr) (ρ : IntervalEnv) (j : ℕ)
    (cfg : DyadicConfig) (J : IntervalRat) : Bool :=
  match dyadicDerivative e ρ j cfg with
  | .error _ => false
  | .ok D => decide (J.lo≤D.toIntervalRat.lo ∧ D.toIntervalRat.hi≤J.hi)

def derivativeEnclosureCheck {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (X : Fin n → IntervalRat) (J : Matrix (Fin n) (Fin n) IntervalRat)
    (p : Fin n → IntervalRat) (cfg : DyadicConfig) : Bool :=
  decide (∀ i j,derivativeEntryCheck (F i) (finBoxEnv (box I X)) j.succ.val cfg (J i j)=true) &&
    decide (∀ i,derivativeEntryCheck (F i) (finBoxEnv (box I X)) 0 cfg (p i)=true)

noncomputable section

theorem derivativeEntryCheck_sound (e : Expr) (ρ : IntervalEnv) (j : ℕ)
    (cfg : DyadicConfig) (J : IntervalRat) (hc : derivativeEntryCheck e ρ j cfg J=true)
    (x : ℕ → ℝ) (hx : ∀ i,x i∈ρ i) (t : ℝ) (ht : t∈ρ j) :
    deriv (Expr.evalAlong e x j) t∈J := by
  cases he : dyadicDerivative e ρ j cfg with
  | error err => simp [derivativeEntryCheck,he] at hc
  | ok D =>
    have hs : succeeded (dyadicDerivative e ρ j cfg)=true := by rw [he]; rfl
    have hd:=dyadicDerivative_mem e ρ j cfg x hx t ht hs
    simp only [derivativeEntryCheck,he,decide_eq_true_eq] at hc
    simp only [outcome,he] at hd
    have hlo : (J.lo : ℝ)≤D.toIntervalRat.lo := by exact_mod_cast hc.1
    have hhi : (D.toIntervalRat.hi : ℝ)≤J.hi := by exact_mod_cast hc.2
    exact ⟨hlo.trans hd.1,hd.2.trans hhi⟩

theorem derivativeEnclosureCheck_sound {n : ℕ} (F : Fin n → Expr)
    (hF : ∀ i,ADSupported (F i)) (I : IntervalRat) (X : Fin n → IntervalRat)
    (J : Matrix (Fin n) (Fin n) IntervalRat) (p : Fin n → IntervalRat) (cfg : DyadicConfig)
    (hc : derivativeEnclosureCheck F I X J p cfg=true)
    {s : ℝ} {x : Fin n → ℝ} (hs : s∈I) (hx : FinBoxMem x X) :
    (∀ i j,jacobian F s x i j∈J i j) ∧ (∀ i,parameterDerivative F s x i∈p i) := by
  simp only [derivativeEnclosureCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
  constructor
  · intro i j
    rw [jacobian_apply F hF]
    apply derivativeEntryCheck_sound (F i) _ j.succ.val cfg (J i j) (hc.1 i j)
      (finEnv (embed s x)) (finEnv_mem_finBoxEnv (embed_mem_box hs hx)) (x j)
    have hb:=finEnv_mem_finBoxEnv (embed_mem_box hs hx) j.succ.val
    simpa only [Fin.val_succ,finEnv_embed_succ,dite_eq_left j.isLt] using hb
  · intro i
    unfold parameterDerivative
    rw [←parameter_evalAlong]
    apply derivativeEntryCheck_sound (F i) _ 0 cfg (p i) (hc.2 i)
      (finEnv (embed s x)) (finEnv_mem_finBoxEnv (embed_mem_box hs hx)) s
    simpa [finBoxEnv,box] using hs

end
end polyak.Numerics.Parametric
