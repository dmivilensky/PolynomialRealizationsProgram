import polyak.Realization.ExplicitSpiral.StationaryTable
import polyak.Realization.ExplicitSpiral.Pairs

/-!
Article: (spirallower), all interpolation pairs of the unchanged-value Y=2 startup.
Use: stationary feasibility, the actual corrected initial pairs, and the actual
initial star inequality assemble one complete infinite interpolation table.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section
open Interpolation

private theorem value_product (z s : ℂ) (C q : ℝ) :
    value z s C=productValue (modeValue z s C) (scalarPosition (response 0 (q^2)) 2) 0 := by
  funext i
  simp [value,productValue]

/-- Article: the actual initial signed pair includes exactly the scalar reserve. -/
theorem initial_pair_identity {z : ℂ} (hz : z≠0) {q : ℝ} (hq : q≠0)
    (C : ℝ) (k : ℕ) (hk : 1≤k) (δ : ℝ) :
    datumR (position z q) (gradient z (multiplier z q) q) (some 0) (some k)+
      δ*datumT (position z q) (gradient z (multiplier z q) q)
        (value z (multiplier z q) C) (some 0) (some k)=
      pairRadius (multiplier z q) (defect z q) (z^k)+
        δ*pairDiscrepancy (multiplier z q) (defect z q) (z^k)
          ((C+2*(multiplier z q).re)/4)+(1-response 0 (q^2) k)^2 := by
  have hn : (some k : Option ℕ)≠some 0 := by simp; omega
  rw [value_product z (multiplier z q) C q]
  simp only [position,gradient,startupPosition,startupGradient,mul_zero,zero_add,
    datumR_product,datumT_product,initialGradient_eq z hz hq]
  simp only [datumR,datumT,correctGradient,hn,↓reduceIte,modePosition,modeGradient,modeValue,
    scalarPosition,response_zero,pow_zero,mul_one,pairRadius,pairDiscrepancy,
    Complex.normSq_eq_norm_sq,norm_one,one_pow]
  ring

/-- Article: the unchanged initial value gives the exact corrected star discrepancy and radius. -/
theorem initial_star_identity {z : ℂ} (hz : z≠0) {q : ℝ} (hq : q≠0) (C : ℝ) :
    datumT (position z q) (gradient z (multiplier z q) q) (value z (multiplier z q) C)
      none (some 0)=C/4-(defect z q).re/2 ∧
    datumR (position z q) (gradient z (multiplier z q) q) none (some 0)=
      (5-Complex.normSq (multiplier z q+defect z q))/4 := by
  rw [value_product z (multiplier z q) C q]
  simp only [position,gradient,startupPosition,startupGradient,mul_zero,zero_add,
    datumR_product,datumT_product,initialGradient_eq z hz hq]
  simp only [datumR,datumT,correctGradient,reduceCtorEq,↓reduceIte,modePosition,
    modeGradient,modeValue,scalarPosition,response_zero,pow_zero,mul_zero,mul_one,
    zero_add,sub_zero,Complex.normSq_eq_norm_sq,norm_one,one_pow,zero_pow,
    ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true]
  constructor
  · simp [Complex.inner]
    ring
  · norm_num
    ring

/-- Article: the complete unchanged-value table follows from exactly its changed pairs. -/
theorem tableFeasible_of_initial {z : ℂ} (hz : z≠0) {q C : ℝ} (hq : q≠0)
    (hbase : TableFeasible (modePosition z) (modeGradient z (multiplier z q))
      (modeValue z (multiplier z q) C))
    (hpairs : ∀ k : ℕ, 1≤k → ∀ δ : ℝ, (δ=1 ∨ δ= -1) →
      0≤pairRadius (multiplier z q) (defect z q) (z^k)+
        δ*pairDiscrepancy (multiplier z q) (defect z q) (z^k)
          ((C+2*(multiplier z q).re)/4)+(1-response 0 (q^2) k)^2)
    (hstar : |C/4-(defect z q).re/2|≤(5-Complex.normSq (multiplier z q+defect z q))/4) :
    TableFeasible (position z q) (gradient z (multiplier z q) q) (value z (multiplier z q) C) := by
  have hs : |datumT (position z q) (gradient z (multiplier z q) q)
      (value z (multiplier z q) C) none (some 0)|≤
        datumR (position z q) (gradient z (multiplier z q) q) none (some 0) := by
    rw [(initial_star_identity hz hq C).1,(initial_star_identity hz hq C).2]
    exact hstar
  have hp (k : ℕ) (hk : 1≤k) :
      |datumT (position z q) (gradient z (multiplier z q) q) (value z (multiplier z q) C)
        (some 0) (some k)|≤datumR (position z q) (gradient z (multiplier z q) q) (some 0) (some k) := by
    have hl := hpairs k hk 1 (Or.inl rfl)
    have hu := hpairs k hk (-1) (Or.inr rfl)
    rw [← initial_pair_identity hz hq C k hk 1] at hl
    rw [← initial_pair_identity hz hq C k hk (-1)] at hu
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  intro i j
  by_cases hi : i=some 0
  · subst i
    cases j with
    | none => rw [datumT_antisymm,abs_neg,datumR_symm]; exact hs
    | some k =>
      by_cases hk : k=0
      · subst k; simp [datumT,datumR]
      · exact hp k (by omega)
  · by_cases hj : j=some 0
    · subst j
      cases i with
      | none => exact hs
      | some k =>
        rw [datumT_antisymm,abs_neg,datumR_symm]
        exact hp k (by simp only [Option.some.injEq] at hi; omega)
    · exact untouched_pair hbase hi hj

/-- Article: radial source data assemble the full explicit initialized table. -/
theorem radial_tableFeasible {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hF : Spiral.spiralPolynomial r q=0)
    (hpairs : ∀ k : ℕ, 1≤k → ∀ δ : ℝ, (δ=1 ∨ δ= -1) →
      0≤pairRadius (multiplier (radialWave r) q) (defect (radialWave r) q) ((radialWave r)^k)+
        δ*pairDiscrepancy (multiplier (radialWave r) q) (defect (radialWave r) q)
          ((radialWave r)^k) (Source.valueConstant r q)+(1-response 0 (q^2) k)^2)
    (hstar : |physicalValueConstant r/4-(defect (radialWave r) q).re/2|≤
      (5-Complex.normSq (multiplier (radialWave r) q+defect (radialWave r) q))/4) :
    TableFeasible (position (radialWave r) q) (gradient (radialWave r) (multiplier (radialWave r) q) q)
      (value (radialWave r) (multiplier (radialWave r) q) (physicalValueConstant r)) := by
  obtain ⟨hn,hn2,hre⟩ := radial_wave_coordinates hr
  have hz : radialWave r≠0 := by intro hz; rw [hz,norm_zero] at hn; linarith
  obtain ⟨hsr,_,_,_⟩ := multiplier_defect_coordinates hr hq hn2 hre
  apply tableFeasible_of_initial hz hq.ne' (stationary_tableFeasible hr hq hF) _ hstar
  intro k hk δ hδ
  have hv : Source.valueConstant r q=(physicalValueConstant r+2*(multiplier (radialWave r) q).re)/4 := by
    rw [hsr]
    rfl
  rw [← hv]
  exact hpairs k hk δ hδ

end
end polyak.Realization.ExplicitSpiral
