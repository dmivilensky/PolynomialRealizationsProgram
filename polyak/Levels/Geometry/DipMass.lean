import polyak.Levels.Lattice.Signs
import polyak.Levels.Geometry.DipSets
import polyak.Levels.Program.Normalization

/-! The dip lemma for every curve and every finite program solution.
The conclusion is positive mass, not merely intersection of supports. -/
noncomputable section
namespace polyak.Levels.Geometry
open MeasureTheory Set Filter

theorem lag_one_neg_iff (Θ : Curve) (ω : Frequency) :
    Θ.lag 1 ω<0 ↔ 0<(ω:ℝ) ∧ (ω:ℝ)/2<Θ ω := by
  have he:=Lattice.lagValue_neg_iff (Θ.pos ω) (Θ.le_pi ω) ω.property.1
    (by linarith [ω.property.2,Real.pi_pos] : (ω:ℝ)<2*Real.pi)
  simp only [Curve.lag,Int.cast_one,one_mul,Lattice.lagValue] at he ⊢
  rw [he]
  constructor <;> rintro ⟨ha,hb⟩ <;> exact ⟨ha,by linarith⟩

/-- The point zero is the only possible zero of lag one outside the closed
dip; this endpoint is excluded by the minimizer constraint in a solution. -/
theorem lag_one_neg_outside (Θ : Curve) {ω : Frequency} (hω : ω∉closedDip Θ)
    (hne : ω≠frequencyZero) : Θ.lag 1 ω<0 := by
  apply (lag_one_neg_iff Θ ω).mpr
  have hn : (ω:ℝ)≠0 := fun h=>hne (Subtype.ext h)
  exact ⟨lt_of_le_of_ne ω.property.1 (Ne.symm hn),lt_of_not_ge hω⟩

theorem solution_closedDip_mass_pos {Θ : Curve} {𝒩 : Set ℤ} {w : Measure Frequency}
    (h : ProgramSolution Θ 𝒩 w) (hone : (1:ℤ)∈𝒩) : 0<w (closedDip Θ) := by
  have : IsFiniteMeasure w:=h.1
  have : NeZero w:=⟨h.2.1⟩
  by_contra hn
  have hz : w (closedDip Θ)=0 := le_antisymm (le_of_not_gt hn) (zero_le : 0≤w (closedDip Θ))
  have hout : ∀ᵐ ω ∂w,ω∉closedDip Θ := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hz
  have hnonpos : ∀ᵐ ω ∂w,Θ.lag 1 ω≤0 := by
    filter_upwards [hout] with ω hω
    by_cases he : ω=frequencyZero
    · simp only [he,Curve.lag_at_zero,le_refl]
    · exact (lag_one_neg_outside Θ hω he).le
  have hi : (∫ ω,Θ.lag 1 ω ∂w)=0 :=
    le_antisymm (integral_nonpos_of_ae hnonpos) (h.2.2.2 1 hone)
  have hnegative : ∀ᵐ ω ∂w,0≤ -Θ.lag 1 ω := hnonpos.mono (fun _ hω=>neg_nonneg.mpr hω)
  have hzAE : (fun ω=> -Θ.lag 1 ω)=ᵐ[w] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnegative (integrable_curve_lag Θ 1 w).neg).mp
      (by rw [integral_neg,hi,neg_zero])
  have hzero : ∀ᵐ ω ∂w,ω=frequencyZero := by
    filter_upwards [hout,hzAE] with ω hω he
    by_contra hh
    have hlt:=lag_one_neg_outside Θ hω hh
    change -Θ.lag 1 ω=0 at he
    linarith
  have he : (∫ ω,Θ.minimizer ω ∂w)=∫ _ : Frequency,(-1:ℝ) ∂w := by
    apply integral_congr_ae
    filter_upwards [hzero] with ω hω
    rw [hω,Curve.minimizer_at_zero]
  rw [integral_const] at he
  have hp:=measureReal_univ_pos (μ:=w)
  simp only [smul_eq_mul,mul_neg,mul_one] at he
  linarith [h.2.2.1]

theorem full_solution_closedDip_mass_pos {Θ : Curve} {w : Measure Frequency}
    (h : ProgramSolution Θ nonzeroLags w) : 0<w (closedDip Θ) :=
  solution_closedDip_mass_pos h (by norm_num [nonzeroLags])

end polyak.Levels.Geometry
