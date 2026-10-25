import polyak.Farey.FanDivergence.Realization

/-! The two-harmonic criterion is an iff for arbitrary actual finite
solution measures carried by the two frequencies, not merely an encoding
of a chosen pair of weights. -/
noncomputable section
namespace polyak.Farey
open polyak.General polyak.Levels MeasureTheory

theorem FanParameters.companion_ne_anchor (P : FanParameters) : P.companion≠P.anchor := by
  intro he
  have hv := congrArg (fun ω : Frequency=>(ω:ℝ)) he
  change 2*Real.pi*((P.p-1:ℤ):ℝ)/(P.k:ℝ)=2*Real.pi*(P.p:ℝ)/(P.k:ℝ) at hv
  have hkR : (P.k:ℝ)≠0 := by exact_mod_cast (ne_of_gt P.k_pos)
  have hh := (div_left_inj' hkR).mp hv
  push_cast at hh
  nlinarith [Real.pi_pos]

def FanSupportedFP (P : FanParameters) (Θ : Curve) : Prop :=
  ∃w : Measure Frequency,ProgramSolution Θ nonzeroLags w ∧
    ∀ᵐω∂w,ω=P.companion ∨ ω=P.anchor

theorem fan_atomic_iff_supported (P : FanParameters) (Θ : Curve) :
    FanAtomicProgram P Θ ↔ FanSupportedFP P Θ := by
  constructor
  · rintro ⟨u,v,_hne,hs⟩
    refine ⟨_,hs,?_⟩
    unfold atomicMeasure
    rw [ae_finsetSum_measure_iff]
    intro j _
    apply Measure.ae_smul_measure
    fin_cases j <;> simp [fanPairFrequencies]
  · rintro ⟨w,hs,hcar⟩
    have : IsFiniteMeasure w := hs.1
    let u : NNReal := (w {P.companion}).toNNReal
    let v : NNReal := (w {P.anchor}).toNNReal
    have hu : (u:ENNReal)=w {P.companion} := ENNReal.coe_toNNReal (measure_ne_top _ _)
    have hv : (v:ENNReal)=w {P.anchor} := ENNReal.coe_toNNReal (measure_ne_top _ _)
    have he := (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac P.companion_ne_anchor).mp hcar
    have hw : atomicMeasure ![u,v] (fanPairFrequencies P)=w := by
      calc
        atomicMeasure ![u,v] (fanPairFrequencies P)=
            (w {P.companion}) • Measure.dirac P.companion+
              (w {P.anchor}) • Measure.dirac P.anchor := by
          simp only [atomicMeasure,Fin.sum_univ_two,fanPairFrequencies,
            Matrix.cons_val_zero,Matrix.cons_val_one,hu,hv]
        _ = w := he.symm
    have hpos : 0<u+v := by
      apply lt_of_le_of_ne (show 0≤u+v from zero_le)
      intro hz
      have hz' : u+v=0 := hz.symm
      have hzR : (u:ℝ)+(v:ℝ)=0 := by exact_mod_cast hz'
      have hu0 : u=0 := by
        apply Subtype.ext
        change (u:ℝ)=0
        nlinarith [u.property,v.property]
      have hv0 : v=0 := by
        apply Subtype.ext
        change (v:ℝ)=0
        nlinarith [u.property,v.property]
      apply hs.2.1
      rw [←hw,hu0,hv0]
      simp only [atomicMeasure,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
        ENNReal.coe_zero,zero_smul,zero_add]
    exact ⟨u,v,hpos,by rw [hw];exact hs⟩

theorem p2_full_program_iff_displayed (P : FanParameters) (hp : P.p=2) (Θ : Curve)
    (hcomp : P.firstAngle<Θ P.companion ∧ Θ P.companion≤P.halfAnchor)
    (hmain : P.firstAngle<Θ P.anchor ∧ Θ P.anchor≤P.halfAnchor) :
    FanSupportedFP P Θ ↔ 0≤fanP2Expression P Θ :=
  (fan_atomic_iff_supported P Θ).symm.trans (p2_atomicProgram_iff_displayed P hp Θ hcomp hmain)

end polyak.Farey
