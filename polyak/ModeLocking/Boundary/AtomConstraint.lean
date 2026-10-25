import polyak.ModeLocking.Boundary.Normalized

/-! The minimizer constraint rules out a heavy atom at the origin, including
for limits that acquire an additional zero atom. -/
noncomputable section
namespace polyak.ModeLocking
open Levels MeasureTheory Set

theorem minimizer_atom_bound {Θ:Curve} {N:Set ℤ} {ν:ProbabilityMeasure Frequency}
    (hν:ProbabilitySolution Θ N ν) (x:Frequency) :
    0≤(ν : Measure Frequency).real {x}*Θ.minimizer x+1-(ν : Measure Frequency).real {x} := by
  have hi := integrable_curve_minimizer Θ (ν : Measure Frequency)
  have hb : (∫ω in ({x} : Set Frequency)ᶜ,Θ.minimizer ω ∂ν)≤
      ∫ω in ({x} : Set Frequency)ᶜ,(1:ℝ) ∂ν := by
    apply integral_mono hi.integrableOn (integrable_const 1)
    intro ω
    exact Real.cos_le_one _
  rw [setIntegral_const,smul_eq_mul,measureReal_compl (measurableSet_singleton x)] at hb
  have he := integral_add_compl (measurableSet_singleton x) hi
  rw [integral_singleton] at he
  have hu : (ν : Measure Frequency).real univ=1 := by simp
  rw [hu,mul_one] at hb
  simp only [smul_eq_mul] at he
  linarith [hν.1]

theorem feasible_heavy_atom_ne_zero {Θ:Curve} {N:Set ℤ} {ν:ProbabilityMeasure Frequency}
    (hν:ProbabilitySolution Θ N ν) {m:ℝ} (hm:1/2<m) {x:Frequency}
    (hx:m≤(ν : Measure Frequency).real {x}) : x≠frequencyZero := by
  intro he
  subst x
  have hb:=minimizer_atom_bound hν frequencyZero
  rw [Θ.minimizer_at_zero] at hb
  linarith

theorem heavy_position_exists {K:ℕ} {q:General.Tuning} (hq:q∈BoundaryInGap K)
    {m:ℝ} (hm:1/2<m)
    (hh:∀ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν→
      ∃x:Frequency,m≤(ν : Measure Frequency).real {x}) :
    ∃x:Frequency,0<(x:ℝ) ∧
      ∀ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν→m≤(ν : Measure Frequency).real {x} := by
  obtain ⟨μ,hμ⟩:=normalized_extremals_nonempty hq
  obtain ⟨x,hx⟩:=hh μ hμ
  have hx0:=feasible_heavy_atom_ne_zero hμ.1 hm hx
  refine ⟨x,lt_of_le_of_ne x.property.1 (fun h=>hx0 (Subtype.ext h.symm)),?_⟩
  intro ν hν
  obtain ⟨y,hy⟩:=hh ν hν
  have he:x=y:=common_heavy_atom hm
    (F:={ρ|NormalizedExtremal q ρ})
    (fun _ hμ _ hν _ _ hu hv huv=>normalized_extremal_mix hμ hν hu hv huv)
    (fun ρ hρ=>hh ρ hρ) hμ hν hx hy
  simpa only [he] using hy

end polyak.ModeLocking
