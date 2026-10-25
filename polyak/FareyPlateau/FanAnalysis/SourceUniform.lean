import polyak.FareyPlateau.FanAnalysis.SourceFamily
import polyak.FareyPlateau.FanAnalysis.UniformFeasibility
import polyak.FareyPlateau.FanAnalysis.UniformNecessity

/-! The literal compact-uniform source statement: one order cutoff for
every tuning of any compact set in a fixed adjacent-lag interval, both
signed Farey families, and both sides of the critical shift. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open General Levels ModeLocking Set MeasureTheory

theorem compact_uniform_fans (S : Set Tuning) (hS : IsCompact S)
    {j k : ℕ} (hk : 3≤k) (hj : 1≤j) (hjk : 2*j<k)
    (b n₁ : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (hn : n₁%(k:ℤ)=b)
    (hinterval : ∀q∈S,(n₁:ℝ)<slopeIndex j k q ∧ slopeIndex j k q<(n₁:ℝ)+k)
    {η : ℝ} (hη : 0<η) :
    ∃L₀ : ℕ,∀q (hq : q∈S),
      let A := intervalAdjacent q hk hj hjk b n₁ hb0 hbk hb hn (hinterval q hq)
      ∀P : Fan.Data,P.j=j → P.k=k → (L₀:ℤ)≤P.L →
        (0<(k:ℝ)-1+Actual.correction A*P.delta ∧
          (Real.toNNReal ((k:ℝ)-1+Actual.correction A*P.delta):ℝ)=
            (k:ℝ)-1+Actual.correction A*P.delta ∧
          ∃a c : Frequency,(a:ℝ)=P.near ∧ (c:ℝ)=P.far ∧
            ProgramSolution (Geometry.shiftedCurve q
              (A.edgeShift-(Actual.critical A-η)*P.delta^2)) nonzeroLags
              (atomicMeasure ![Real.toNNReal ((k:ℝ)-1+Actual.correction A*P.delta),1] ![a,c])) ∧
        (∀a c : Frequency,(a:ℝ)=P.near → (c:ℝ)=P.far →
          ¬∃μ : Measure Frequency,ProgramSolution
            (Geometry.shiftedCurve q (A.edgeShift-(Actual.critical A+η)*P.delta^2)) nonzeroLags μ ∧
              (∀ᵐω∂μ,ω=a ∨ ω=c)) := by
  classical
  let _ : CompactSpace S := isCompact_iff_compactSpace.mp hS
  cases isEmpty_or_nonempty S with
  | inl h =>
    exact ⟨0,fun q hq=>isEmptyElim (⟨q,hq⟩:S)⟩
  | inr h =>
    let B := sourceFamily S hk hj hjk b n₁ hb0 hbk hb hn hinterval
    obtain ⟨La,hLa⟩ := B.uniform_fan_feasible hη
    obtain ⟨Lb,hLb⟩ := B.uniform_no_measure hη
    refine ⟨max La Lb,?_⟩
    intro q hq
    dsimp only
    intro P hjP hkP hPL
    let x : S := ⟨q,hq⟩
    have hLa0 : (La:ℤ)≤((max La Lb:ℕ):ℤ) := by exact_mod_cast (le_max_left La Lb)
    have hLb0 : (Lb:ℤ)≤((max La Lb:ℕ):ℤ) := by exact_mod_cast (le_max_right La Lb)
    have hLaP : (La:ℤ)≤P.L := hLa0.trans hPL
    have hLbP : (Lb:ℤ)≤P.L := hLb0.trans hPL
    have ha := hLa x P hjP hkP hLaP
    have hno := hLb x P hjP hkP hLbP
    have hz : B.correction x=Actual.correction (B.adjacent x) := B.correction_actual x
    rw [hz] at ha
    refine ⟨⟨ha.1,Real.coe_toNNReal _ ha.1.le,ha.2⟩,hno⟩

end polyak.FareyPlateau.FanAnalysis
