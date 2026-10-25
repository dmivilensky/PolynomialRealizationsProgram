import polyak.FareyPlateau.Ray.ThresholdDefinition

/-! The infimum in a_F has a common finite lower bound before any
nonresonant curvature comparison is used. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set

theorem SourceCertificate.R_neg_one {j k : ℕ} {b : ℤ} {D : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1) :
    C.R (-1)=edgeFace (Chart.rationalCosine j k) (Chart.rationalHeight j k) (-1) D := by
  have hω := Regions.rationalAngle_mem hj hjk
  have hc : -1<Chart.rationalCosine j k := by
    have hx := Real.cos_lt_cos_of_nonneg_of_le_pi hω.1.le le_rfl hω.2
    simpa only [Chart.rationalCosine,Real.cos_pi] using hx
  rw [C.off_contact hj hjk hb hc.ne,Symbols.psi_neg_one,sub_zero]
  rfl

theorem maxima_bddBelow {j k : ℕ} {b : ℤ} (D : ℝ)
    (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1) :
    BddBelow (Set.range (SourceCertificate.maximum (j:=j) (k:=k) (b:=b) (D:=D))) := by
  refine ⟨edgeFace (Chart.rationalCosine j k) (Chart.rationalHeight j k) (-1) D,?_⟩
  rintro z ⟨C,rfl⟩
  rw [←C.R_neg_one hj hjk hb]
  exact C.maximum_spec.2 (-1) (by norm_num)

theorem aF_le_maximum {j k : ℕ} {b : ℤ} {D : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1) :
    aF j k b D≤C.maximum := csInf_le (maxima_bddBelow D hj hjk hb) ⟨C,rfl⟩

theorem aF_lt_iff {j k : ℕ} {b : ℤ} {D a : ℝ}
    (hj : 1≤j) (hjk : 2*j<k) (hb : (b*j)%k=1)
    (hn : Nonempty (SourceCertificate j k b D)) :
    aF j k b D<a ↔ ∃C : SourceCertificate j k b D,C.maximum<a := by
  have hr : (Set.range (SourceCertificate.maximum (j:=j) (k:=k) (b:=b) (D:=D))).Nonempty := by
    obtain ⟨C⟩ := hn
    exact ⟨C.maximum,⟨C,rfl⟩⟩
  rw [aF,csInf_lt_iff (maxima_bddBelow D hj hjk hb) hr]
  constructor
  · rintro ⟨z,⟨C,rfl⟩,hC⟩; exact ⟨C,hC⟩
  · rintro ⟨C,hC⟩; exact ⟨C.maximum,⟨C,rfl⟩,hC⟩

end polyak.FareyPlateau.Ray
