import polyak.FareyPlateau.Ray.SecondContact
import polyak.FareyPlateau.Ray.Endpoints

/-! The complete scalar equivalence in Lemma ray, including both endpoint
tests and the strict second derivative at the forced contact. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set
open scoped BigOperators

theorem SourceCertificate.curvature_iff {j k : ℕ} {b : ℤ} {D a : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    deriv^[2] (LargeCurvature.indexedSymbol q 0 C.lag C.weight) (Regions.rationalAngle j k)<0 ↔
      C.R (Chart.rationalCosine j k)<a := by
  rw [C.second_contact hj hjk hb q he]
  have hω := Regions.rationalAngle_mem hj hjk
  have hk : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hγ : 0<Real.sin (Real.pi/k) := Real.sin_pos_of_pos_of_lt_pi
    (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hk)
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hμ := oneMass_pos C.admissible
  have hp : 0<4*(Real.sin (Real.pi/k))^3*Real.sin (Regions.rationalAngle j k)*
      oneMass k b C.lag C.weight := by positivity
  rw [lt_iff_not_ge,mul_nonneg_iff_of_pos_left hp,not_le,sub_neg]

theorem SourceCertificate.ray_criterion {j k : ℕ} {b : ℤ} {D a : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    C.maximum<a ↔
      (∀x : ℝ,0<x → x≤Real.pi → x≠Regions.rationalAngle j k →
        LargeCurvature.indexedSymbol q 0 C.lag C.weight x<0) ∧
      deriv^[2] (LargeCurvature.indexedSymbol q 0 C.lag C.weight) (Regions.rationalAngle j k)<0 ∧
      0<∑i,C.weight i*(C.lag i:ℝ)*((C.lag i:ℝ)+2*Geometry.tau q) := by
  have hω := Regions.rationalAngle_mem hj hjk
  rw [C.maximum_lt_iff,C.curvature_iff hj hjk hb q he,C.endpoint_iff hj hjk hb q he]
  constructor
  · intro h
    refine ⟨?_,h _ ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩,h 1 (by norm_num)⟩
    intro x hx hxπ hne
    rcases eq_or_lt_of_le hxπ with heq|hlt
    · rw [heq]
      exact C.strict_pi q
    · have hc : Real.cos x≠Chart.rationalCosine j k := by
        intro hc
        have heq := Real.strictAntiOn_cos.injOn ⟨hx.le,hlt.le⟩ ⟨hω.1.le,hω.2.le⟩ hc
        exact hne heq
      apply (C.interior_ray_iff hj hjk hb q he ⟨hx,hlt⟩ hc).mpr
      exact h _ ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  · rintro ⟨hstrict,hcurv,hend⟩ c hc
    by_cases hneg : c= -1
    · rw [hneg]; exact C.R_neg_one_lt hj hjk hb q he
    by_cases hone : c=1
    · rw [hone]; exact hend
    by_cases hcontact : c=Chart.rationalCosine j k
    · rw [hcontact]; exact hcurv
    let x := Real.arccos c
    have hx : x∈Ioo (0:ℝ) Real.pi :=
      ⟨Real.arccos_pos.mpr (lt_of_le_of_ne hc.2 hone),
        Real.arccos_lt_pi.mpr (lt_of_le_of_ne hc.1 (Ne.symm hneg))⟩
    have hcos : Real.cos x=c := Real.cos_arccos hc.1 hc.2
    have hne : x≠Regions.rationalAngle j k := by
      intro hh
      apply hcontact
      rw [←hcos,hh]
      rfl
    have hcosne : Real.cos x≠Chart.rationalCosine j k := by rwa [hcos]
    have ht := (C.interior_ray_iff hj hjk hb q he hx hcosne).mp (hstrict x hx.1 hx.2.le hne)
    rwa [hcos] at ht

end polyak.FareyPlateau.Ray
