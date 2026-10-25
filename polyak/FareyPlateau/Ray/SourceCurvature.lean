import polyak.FareyPlateau.Ray.SourceA2

/-! The complete source a₂ comparison and the original edge-symbol
curvature formula, with the unique full multiplier in the equality case. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set
open scoped BigOperators Classical

theorem SourceCertificate.source_sharp {K j k : ℕ} {b : ℤ} {D : ℝ}
    (C : SourceCertificate j k b D) (hK : 2≤K) (hf : Chart.FractionInWindow K j k)
    (hb : (b*j)%k=1)
    (hres : ∀m : ℤ,edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D≠(b:ℝ)+m*k) :
    a2 j k b D≤C.R (Chart.rationalCosine j k) :=
  source_sharp_curvature hK hf hb (floor_adjacent hf.1 b _ hres).1
    (floor_adjacent hf.1 b _ hres).2.1 (lowerLag_class k b _)
    (floor_adjacent hf.1 b _ hres).2.2 C

theorem SourceCertificate.source_sharp_eq_iff {K j k : ℕ} {b : ℤ} {D : ℝ}
    (C : SourceCertificate j k b D) (hK : 2≤K) (hf : Chart.FractionInWindow K j k)
    (hb : (b*j)%k=1)
    (hres : ∀m : ℤ,edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D≠(b:ℝ)+m*k) :
    C.R (Chart.rationalCosine j k)=a2 j k b D ↔
      ∀l : ℤ,LargeCurvature.supportWeight C.lag C.weight l=
        if l=lowerLag k b (edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D)
        then 1-edgeFraction k b (edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D)
        else if l=lowerLag k b (edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D)+k
        then edgeFraction k b (edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D) else 0 := by
  let n₁ := lowerLag k b (edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D)
  let t := edgeFraction k b (edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D)
  have ht := floor_adjacent hf.1 b _ hres
  constructor
  · exact source_sharp_equality hK hf hb ht.1 ht.2.1 (lowerLag_class k b _) ht.2.2 C
  · intro hw
    have hsupp (i) : C.lag i=n₁ ∨ C.lag i=n₁+k := by
      by_contra hh
      have h₁ : C.lag i≠n₁ := fun h=>hh (Or.inl h)
      have h₂ : C.lag i≠n₁+k := fun h=>hh (Or.inr h)
      have hi := hw (C.lag i)
      rw [LargeCurvature.supportWeight_at C.admissible.injective,ite_eq_right h₁,ite_eq_right h₂] at hi
      exact (C.admissible.positive i).ne' hi
    obtain ⟨q,he,_⟩ := source_edge_exists_unique hK hf (lt_add_one (aE K j k D))
    obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
    exact (C.sharp_curvature_eq_iff (by omega) hjk hb ht.1 ht.2.1
      (lowerLag_class k b _) ht.2.2 q he).mpr hsupp

theorem edgeSymbol_oneMass {j k : ℕ} {b : ℤ} {D : ℝ} (hk : 0<k) (hb : (b*j)%k=1)
    (hres : ∀m : ℤ,edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D≠(b:ℝ)+m*k) :
    oneMass k b (edgeSymbol hk hb hres).lag (edgeSymbol hk hb hres).weight=1 := by
  have hclass (i : Fin 2) : (edgeSymbol hk hb hres).lag i%k=b%k := by
    fin_cases i
    · exact lowerLag_class k b _
    · change (lowerLag k b _+(k:ℤ))%k=b%k
      rw [Int.add_emod_right]
      exact lowerLag_class k b _
  have hone : oneClass k b (edgeSymbol hk hb hres).lag=Finset.univ :=
    Finset.filter_eq_self.mpr (fun i _=>hclass i)
  rw [oneMass,hone]
  exact (edgeSymbol hk hb hres).admissible.normalization

def edgeF {j k : ℕ} {b : ℤ} {D : ℝ} (q : Tuning) (C : SourceCertificate j k b D) : ℝ→ℝ :=
  fun x=>-(1/2:ℝ)*LargeCurvature.indexedSymbol q 0 C.lag C.weight x

theorem edgeF_curvature {K j k : ℕ} {b : ℤ} {D a : ℝ}
    (hK : 2≤K) (hf : Chart.FractionInWindow K j k) (hb : (b*j)%k=1)
    (hres : ∀m : ℤ,edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D≠(b:ℝ)+m*k)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    deriv^[2] (edgeF q (edgeSymbol hf.1 hb hres)) (Regions.rationalAngle j k)=
      2*Real.sin (Regions.rationalAngle j k)*(Real.sin (Real.pi/k))^3*(a-a2 j k b D) := by
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  have hh := (edgeSymbol hf.1 hb hres).second_contact (by omega) hjk hb q he
  rw [edgeSymbol_oneMass,edgeSymbol_contact hK hf hb hres] at hh
  change deriv^[2] (fun x=>-(1/2:ℝ)*LargeCurvature.indexedSymbol q 0
    (edgeSymbol hf.1 hb hres).lag (edgeSymbol hf.1 hb hres).weight x) _=_
  rw [←iteratedDeriv_eq_iterate,iteratedDeriv_const_mul_field,iteratedDeriv_eq_iterate,hh]
  ring

end polyak.FareyPlateau.Ray
