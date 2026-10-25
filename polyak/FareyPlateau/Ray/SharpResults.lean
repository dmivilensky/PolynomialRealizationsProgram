import polyak.FareyPlateau.Ray.AdjacentCertificate
import polyak.FareyPlateau.Ray.UniqueAdjacentWeights
import polyak.FareyPlateau.Ray.Infimum

/-! The source sharp bound, its unique multiplier, and the induced lower
bound for the actual unrestricted threshold a_F. No tuning is an input. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set

theorem source_sharp_curvature {K j k : ℕ} {b n₁ : ℤ} {D t : ℝ}
    (hK : 2≤K) (hf : Chart.FractionInWindow K j k) (hb : (b*j)%k=1)
    (ht0 : 0<t) (ht1 : t<1) (hn₁ : n₁%k=b%k)
    (hbar : edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D=(n₁:ℝ)+t*k)
    (C : SourceCertificate j k b D) :
    edgeA2 (Regions.rationalAngle j k) (Real.pi/k) k D t≤C.R (Chart.rationalCosine j k) := by
  obtain ⟨q,he,_⟩ := source_edge_exists_unique hK hf
    (lt_add_one (aE K j k D))
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  exact C.sharp_curvature (by omega) hjk hb ht0 ht1 hn₁ hbar q he

theorem source_sharp_equality {K j k : ℕ} {b n₁ : ℤ} {D t : ℝ}
    (hK : 2≤K) (hf : Chart.FractionInWindow K j k) (hb : (b*j)%k=1)
    (ht0 : 0<t) (ht1 : t<1) (hn₁ : n₁%k=b%k)
    (hbar : edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D=(n₁:ℝ)+t*k)
    (C : SourceCertificate j k b D)
    (heq : C.R (Chart.rationalCosine j k)=edgeA2 (Regions.rationalAngle j k) (Real.pi/k) k D t) :
    ∀l : ℤ,LargeCurvature.supportWeight C.lag C.weight l=
      if l=n₁ then 1-t else if l=n₁+k then t else 0 := by
  obtain ⟨q,he,_⟩ := source_edge_exists_unique hK hf
    (lt_add_one (aE K j k D))
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  exact C.adjacent_weights hf.1 hb hn₁ hbar
    ((C.sharp_curvature_eq_iff (by omega) hjk hb ht0 ht1 hn₁ hbar q he).mp heq)

theorem adjacent_contact_value {K j k : ℕ} {b n₁ : ℤ} {D t : ℝ}
    (hK : 2≤K) (hf : Chart.FractionInWindow K j k) (hb : (b*j)%k=1)
    (ht0 : 0<t) (ht1 : t<1) (hn₁ : n₁%k=b%k)
    (hbar : edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D=(n₁:ℝ)+t*k) :
    (adjacentCertificate hf.1 hb hn₁ ht0 ht1 hbar).R (Chart.rationalCosine j k)=
      edgeA2 (Regions.rationalAngle j k) (Real.pi/k) k D t := by
  obtain ⟨q,he,_⟩ := source_edge_exists_unique hK hf
    (lt_add_one (aE K j k D))
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  apply ((adjacentCertificate hf.1 hb hn₁ ht0 ht1 hbar).sharp_curvature_eq_iff
    (by omega) hjk hb ht0 ht1 hn₁ hbar q he).mpr
  intro i
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem a2_le_aF {K j k : ℕ} {b n₁ : ℤ} {D t : ℝ}
    (hK : 2≤K) (hf : Chart.FractionInWindow K j k) (hb : (b*j)%k=1)
    (ht0 : 0<t) (ht1 : t<1) (hn₁ : n₁%k=b%k)
    (hbar : edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D=(n₁:ℝ)+t*k) :
    edgeA2 (Regions.rationalAngle j k) (Real.pi/k) k D t≤aF j k b D := by
  apply le_csInf
  · exact ⟨_,⟨adjacentCertificate hf.1 hb hn₁ ht0 ht1 hbar,rfl⟩⟩
  · rintro z ⟨C,rfl⟩
    exact (source_sharp_curvature hK hf hb ht0 ht1 hn₁ hbar C).trans
      (C.maximum_spec.2 _ ⟨(rationalCosine_mem hK hf).1.le,(rationalCosine_mem hK hf).2.le⟩)

end polyak.FareyPlateau.Ray
