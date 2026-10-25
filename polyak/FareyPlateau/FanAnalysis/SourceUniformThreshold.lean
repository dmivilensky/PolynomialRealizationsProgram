import polyak.FareyPlateau.FanAnalysis.SourceUniform
import polyak.FareyPlateau.FanAnalysis.PairAsymptotic

/-! The restricted optimum has the literal compact-uniform little-o expansion.
The common error bound is derived from the actual constructive and arbitrary
measure halves of the fan theorem, rather than assumed as family data. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open General Levels ModeLocking Set MeasureTheory

theorem compact_uniform_pair_threshold (S : Set Tuning) (hS : IsCompact S)
    {j k : ℕ} (hk : 3≤k) (hj : 1≤j) (hjk : 2*j<k)
    (b n₁ : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (hn : n₁%(k:ℤ)=b)
    (hinterval : ∀q∈S,(n₁:ℝ)<slopeIndex j k q ∧ slopeIndex j k q<(n₁:ℝ)+k)
    {η : ℝ} (hη : 0<η) :
    ∃L₀ : ℕ,∀q (hq : q∈S),
      let A := intervalAdjacent q hk hj hjk b n₁ hb0 hbk hb hn (hinterval q hq)
      ∀P : Fan.Data,P.j=j → P.k=k → (L₀:ℤ)≤P.L →
        ∀a c : Frequency,(a:ℝ)=P.near → (c:ℝ)=P.far →
          |pairThreshold q a c-A.edgeShift+Actual.critical A*P.delta^2|≤η*P.delta^2 := by
  obtain ⟨L₀,hL₀⟩ := compact_uniform_fans S hS hk hj hjk b n₁ hb0 hbk hb hn hinterval hη
  refine ⟨L₀,?_⟩
  intro q hq
  dsimp only
  intro P hjP hkP hPL a c ha hc
  let A := intervalAdjacent q hk hj hjk b n₁ hb0 hbk hb hn (hinterval q hq)
  have hfan := hL₀ q hq P hjP hkP hPL
  obtain ⟨a',c',ha',hc',hsol⟩ := hfan.1.2.2
  have hae : a'=a := Subtype.ext (ha'.trans ha.symm)
  have hce : c'=c := Subtype.ext (hc'.trans hc.symm)
  subst a'
  subst c'
  have hupper : pairFP (Geometry.shiftedCurve q (A.edgeShift-(Actual.critical A-η)*P.delta^2)) a c := by
    refine ⟨_,hsol,?_⟩
    unfold atomicMeasure
    rw [ae_finsetSum_measure_iff]
    intro i _
    apply Measure.ae_smul_measure
    fin_cases i <;> simp [pairCarrier]
  have hlower : ¬pairFP (Geometry.shiftedCurve q (A.edgeShift-(Actual.critical A+η)*P.delta^2)) a c :=
    hfan.2 a c ha hc
  exact pairThreshold_error_bound q a c (delta_ne_zero P) hupper hlower

end polyak.FareyPlateau.FanAnalysis
