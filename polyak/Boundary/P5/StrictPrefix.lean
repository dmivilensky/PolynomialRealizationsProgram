import polyak.Boundary.P5.ContinuationBounds

/-! All inactive finite P5 constraints are strictly positive at positive h. -/
noncomputable section
namespace polyak.Boundary.P5
open LeanCert.Core LeanCert.Engine Numerics.Parametric

theorem lagCheck_pos {n : ℕ} (hn : 1≤n) (code : LagCode n) (positive : Bool)
    (I : IntervalRat) (X : Fin 7 → IntervalRat) (cfg : DyadicConfig)
    (hc : lagCheck n code positive I X cfg=true)
    {h : ℝ} {Z : Coordinates} (hh : 0<h) (hs : h∈I) (hX : FinBoxMem Z X)
    (ha : ¬ActivePair n (lagSign positive)) : 0<actualPrimal h Z n (lagSign positive) := by
  have hb : ¬activeLag n positive=true := fun ht => ha ((activeLag_iff n positive).mp ht)
  simp only [lagCheck,hb] at hc
  have hp := boundCheck_sound (prefixExpr n code positive) I X cfg true hc hs hX
  change 0<eval (prefixExpr n code positive) h Z at hp
  rw [actualPrimal_eq_raw_div hh.le Z hn]
  apply div_pos _ (lagDenominator_pos (by linarith : (1 : ℝ)≤1+h) n hn)
  rw [rawBranch_division n code]
  by_cases hk : criticalLag n positive=true
  · rw [critical_actualRaw_zero hn ((criticalLag_iff n positive).mp hk),zero_add]
    simp only [prefixExpr,hk,↓reduceIte,dividedSlackExpr_eval] at hp
    exact mul_pos hh hp
  · rw [noncritical_actualRaw_eq hn (lagSign_sign positive)
      (fun hf => hk ((criticalLag_iff n positive).mpr hf))]
    have hk' : criticalLag n positive=false := Bool.eq_false_iff.mpr hk
    simp only [prefixExpr,hk',Bool.false_eq_true,↓reduceIte] at hp
    change 0<((3/2 : ℚ) : ℝ)+h*eval (dividedSlackExpr n code (lagSign positive)) h Z at hp
    rw [dividedSlackExpr_eval] at hp
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hp
    exact hp

theorem prefixCheck_pos (codes : (n : Fin 24) → LagCode n)
    (I : IntervalRat) (cert : WeightedCertificate 7) (cfg : DyadicConfig)
    (hc : prefixCheck codes I cert cfg=true)
    {h : ℝ} {Z : Coordinates} (hh : 0<h) (hs : h∈I)
    (hX : FinBoxMem Z (coordinateBox cert.center cert.radius))
    {n : ℕ} (hn : 1≤n) (hn24 : n<24) {σ : ℝ} (hσ : σ= -1 ∨ σ=1)
    (ha : ¬ActivePair n σ) : 0<actualPrimal h Z n σ := by
  simp only [prefixCheck,decide_eq_true_eq] at hc
  rcases hσ with rfl | rfl
  · simpa [lagSign] using lagCheck_pos hn (codes ⟨n,hn24⟩) false I _ cfg
      (hc ⟨n,hn24⟩ false hn) hh hs hX (by simpa [lagSign] using ha)
  · simpa [lagSign] using lagCheck_pos hn (codes ⟨n,hn24⟩) true I _ cfg
      (hc ⟨n,hn24⟩ true hn) hh hs hX (by simpa [lagSign] using ha)

theorem continuation_inactive_prefix_pos {h : ℝ} (hh : h∈Set.Ioc (0 : ℝ) (11791/500000))
    {n : ℕ} (hn : 1≤n) (hn24 : n<24) {σ : ℝ} (hσ : σ= -1 ∨ σ=1)
    (ha : ¬ActivePair n σ) : 0<actualPrimal h (Selection.continuation h) n σ := by
  obtain ⟨slab,hm,hs,hX⟩ := continuation_checkedBox ⟨hh.1.le,hh.2⟩
  have hc := List.all_eq_true.mp Certificates.Continuation.P5Properties.prefixAccepted slab hm
  exact prefixCheck_pos Certificates.Continuation.P5Lags.codes slab.domain slab.certificate
    {precision:=-80} hc hh.1 hs hX hn hn24 hσ ha

end polyak.Boundary.P5
