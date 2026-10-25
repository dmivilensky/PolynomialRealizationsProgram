import polyak.Levels.Chart.GapCharacterization

/-! Proposition chart(b): the explicit ordered-root coordinates are an
actual homeomorphism of the original geometric gap. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set

abbrev ParameterSpace := ℝ×ℝ×ℝ

def gapParameterSet (K : ℕ) : Set ParameterSpace :=
  {p | boundaryCosine K<p.2.1 ∧ p.2.1<p.2.2 ∧ p.2.2<boundaryCosine (K+1) ∧
    amplitudeFloor p.2.1 p.2.2<p.1}

abbrev GapParameters (K : ℕ) := {p : ParameterSpace // p∈gapParameterSet K}
abbrev GapTunings (K : ℕ) := {q : Tuning // Geometry.Gap K q}

def coordinates (q : Tuning) : ParameterSpace :=
  (-(coefficients q).c2,leftRoot (coefficients q),rightRoot (coefficients q))

theorem coordinates_of_polynomial (q : Tuning) {a r₁ r₂ : ℝ}
    (ha : 0<a) (hr : r₁≤r₂) (he : coefficients q=gapPolynomial a r₁ r₂) :
    coordinates q=(a,r₁,r₂) := by
  unfold coordinates
  rw [he,leftRoot_gapPolynomial ha hr,rightRoot_gapPolynomial ha hr]
  simp only [gapPolynomial,neg_neg]

theorem coordinates_mem {K : ℕ} (q : GapTunings K) : coordinates q.val∈gapParameterSet K := by
  obtain ⟨a,r₁,r₂,h₁,hr,h₂,ha,he⟩ := root_coordinates_of_gap q.val q.property
  have hu := h₂.trans (boundaryCosine_succ_lt_one q.property.1)
  have hap : 0<a := (amplitudeFloor_pos (hr.trans hu) hu).trans ha
  rw [coordinates_of_polynomial q.val hap hr.le he]
  exact ⟨h₁,hr,h₂,ha⟩

def gapCoefficientPoint {K : ℕ} (hK : 2≤K) (p : GapParameters K) : CoefficientPoint :=
  ⟨gapPolynomial p.val.1 p.val.2.1 p.val.2.2,
    gapPolynomial_mem_domain ((boundaryCosine_ge_neg_one K).trans_lt p.property.1)
      p.property.2.1.le (p.property.2.2.1.trans (boundaryCosine_succ_lt_one hK)) p.property.2.2.2⟩

def gapInverse {K : ℕ} (hK : 2≤K) (p : GapParameters K) : GapTunings K :=
  ⟨inverseTuning (gapCoefficientPoint hK p),gap_of_root_coordinates _ hK
    p.property.1 p.property.2.1 p.property.2.2.1 p.property.2.2.2
    (coefficients_inverseTuning (gapCoefficientPoint hK p))⟩

theorem coordinates_gapInverse {K : ℕ} (hK : 2≤K) (p : GapParameters K) :
    coordinates (gapInverse hK p).val=p.val := by
  have hu := p.property.2.2.1.trans (boundaryCosine_succ_lt_one hK)
  have hap : 0<p.val.1 :=
    (amplitudeFloor_pos (p.property.2.1.trans hu) hu).trans p.property.2.2.2
  exact coordinates_of_polynomial _ hap p.property.2.1.le
    (coefficients_inverseTuning (gapCoefficientPoint hK p))

theorem gapInverse_coordinates {K : ℕ} (hK : 2≤K) (q : GapTunings K) :
    (gapInverse hK ⟨coordinates q.val,coordinates_mem q⟩).val=q.val := by
  obtain ⟨a,r₁,r₂,h₁,hr,h₂,ha,he⟩ := root_coordinates_of_gap q.val q.property
  have hu := h₂.trans (boundaryCosine_succ_lt_one hK)
  have hap : 0<a := (amplitudeFloor_pos (hr.trans hu) hu).trans ha
  apply coefficients_injective (inverseBeta_pos _)
    (roots_of_nonempty_dip q.val q.property.2.1).1
  change coefficients (inverseTuning _)=coefficients q.val
  rw [coefficients_inverseTuning]
  change gapPolynomial (coordinates q.val).1 (coordinates q.val).2.1
    (coordinates q.val).2.2=coefficients q.val
  rw [coordinates_of_polynomial q.val hap hr.le he]
  exact he.symm

@[fun_prop] theorem continuous_gapPolynomial :
    Continuous (fun p : ParameterSpace=>gapPolynomial p.1 p.2.1 p.2.2) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun p : ParameterSpace=>(1-p.1*p.2.1*p.2.2,1+p.1*(p.2.1+p.2.2),-p.1))
  fun_prop

theorem continuous_gapCoefficientPoint {K : ℕ} (hK : 2≤K) : Continuous (gapCoefficientPoint hK) := by
  apply Continuous.subtype_mk
  exact continuous_gapPolynomial.comp continuous_subtype_val

theorem continuous_gap_coordinates {K : ℕ} :
    Continuous (fun q : GapTunings K=>coordinates q.val) := by
  have hc : Continuous (fun q : GapTunings K=>coefficients q.val) :=
    continuous_coefficients.comp continuous_subtype_val
  have hn (q : GapTunings K) : (coefficients q.val).c2≠0 := by
    have hβ := (roots_of_nonempty_dip q.val q.property.2.1).1
    exact ne_of_lt ((coefficient_quadratic_neg_iff q.val).mpr hβ)
  have hl : ContinuousOn (fun q : GapTunings K=>leftRoot (coefficients q.val)) univ :=
    continuousOn_leftRoot.comp hc.continuousOn (fun q _=>hn q)
  have hr : ContinuousOn (fun q : GapTunings K=>rightRoot (coefficients q.val)) univ :=
    continuousOn_rightRoot.comp hc.continuousOn (fun q _=>hn q)
  exact (Coefficients.continuous_c2.comp hc).neg.prodMk
    ((continuousOn_univ.mp hl).prodMk (continuousOn_univ.mp hr))

def gapHomeomorph {K : ℕ} (hK : 2≤K) : GapTunings K ≃ₜ GapParameters K where
  toFun q := ⟨coordinates q.val,coordinates_mem q⟩
  invFun := gapInverse hK
  left_inv q := Subtype.ext (gapInverse_coordinates hK q)
  right_inv p := Subtype.ext (coordinates_gapInverse hK p)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_gap_coordinates
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_inverseTuning.comp (continuous_gapCoefficientPoint hK)

end polyak.Levels.Chart
