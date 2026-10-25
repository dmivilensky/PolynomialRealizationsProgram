import polyak.FareyPlateau.Ray.Criterion
import polyak.FareyPlateau.Edge.Persistence

/-! The ray criterion constructs primary regularity data and therefore
the actual threshold and its persistent singleton extremals. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels ModeLocking Set Filter MeasureTheory
open scoped BigOperators Topology

theorem source_atom_value {j k : ℕ} (hk : 0<k) (hjk : 2*j≤k) :
    (Edge.atom j k hk hjk:ℝ)=Regions.rationalAngle j k := by
  dsimp [Edge.atom,Farey.gridFrequency,Regions.rationalAngle]
  push_cast
  ring

def SourceCertificate.edgeCertificate {j k : ℕ} {b : ℤ} {D a : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k)
    (hb0 : 0<b) (hbk : b<k) (hb : (b*j)%k=1)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D)
    (ha : C.maximum<a) : Edge.Certificate q 0 j k := by
  have hscalar := (C.ray_criterion hj hjk hb q he).mp ha
  have hk : 3≤k := by omega
  have hbmod : b%k=b := Int.emod_eq_of_lt hb0.le hbk
  have hinv : b*(j:ℤ)≡1 [ZMOD (k:ℤ)] := by
    change (b*j)%k=1%k
    rw [hb,Int.emod_eq_of_lt (by norm_num : (0:ℤ)≤1) (by omega : (1:ℤ)<k)]
  have hclass : ∀i,C.lag i%(k:ℤ)=0 ∨ C.lag i%(k:ℤ)=b := by
    intro i
    have hp := C.admissible.positions i
    rw [hbmod] at hp
    exact hp.symm
  have hpair : ∃i l,C.lag i≠C.lag l ∧ C.lag i%(k:ℤ)=b ∧ C.lag l%(k:ℤ)=b := by
    obtain ⟨i,l,hne,hi,hl⟩ := C.admissible.two_one
    rw [hbmod] at hi hl
    exact ⟨i,l,hne,hi,hl⟩
  have hphase : Geometry.shiftedCurve q 0 (Edge.atom j k (by omega) hjk.le)=Real.pi/k := by
    rw [Geometry.shiftedCurve_zero]
    change q.angle (Edge.atom j k (by omega) hjk.le)=Real.pi/k
    rw [source_atom_value]
    exact source_edge_phase q hj hjk he
  exact LargeCurvature.indexedCertificate hk hj hjk b hb0 hbk hinv C.lag C.weight
    C.admissible.injective C.admissible.nonzero C.admissible.positive C.admissible.normalization
    hclass hpair hphase
    (by intro x hx hxπ hne; rw [source_atom_value] at hne; exact hscalar.1 x hx hxπ hne)
    (by rw [source_atom_value]; exact hscalar.2.1) hscalar.2.2

theorem SourceCertificate.regular_threshold {j k : ℕ} {b : ℤ} {D a : ℝ}
    (C : SourceCertificate j k b D) (hj : 1≤j) (hjk : 2*j<k)
    (hb0 : 0<b) (hbk : b<k) (hb : (b*j)%k=1)
    (q : Tuning) (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D)
    (ha : C.maximum<a) :
    RegularPoint q 0 k ∧ Threshold.sigma q=0 ∧ Threshold.sigmaPeriodic q k=0 := by
  let E := C.edgeCertificate hj hjk hb0 hbk hb q he ha
  exact ⟨E.regular,E.sigma_eq,E.sigmaPeriodic_eq⟩

end polyak.FareyPlateau.Ray
