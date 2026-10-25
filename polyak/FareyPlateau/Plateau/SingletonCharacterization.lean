import polyak.FareyPlateau.Plateau.RegularSourceCertificate
import polyak.FareyPlateau.Plateau.SingletonGap
import polyak.FareyPlateau.Domain.Recovery
import polyak.FareyPlateau.LargeCurvature.Results

/-! Exact classification of every regular singleton, in the actual tuning
space, by the literal a_E and unrestricted a_F thresholds. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels ModeLocking Set

def singletonRoof (K j k : ℕ) (b : ℤ) (D : ℝ) : ℝ :=
  max (aE K j k D) (Ray.aF j k b D)

def RegularSingletonAt (j k : ℕ) (hk : 0<k) (hjk : 2*j≤k) (q : Tuning) : Prop :=
  ∃L : ℕ,∃R : RegularData q 0 L,Set.range R.atoms={Edge.atom j k hk hjk}

theorem inverse_mod_value {j k : ℕ} {b : ℤ} (hk : 3≤k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) : (b*j)%k=1 := by
  simpa only [Int.ModEq,Int.emod_eq_of_lt (by norm_num : (0:ℤ)≤1)
    (by omega : (1:ℤ)<k)] using hb

theorem singleton_of_roof {K j k : ℕ} (hK : 2≤K) (hf : Chart.FractionInWindow K j k)
    (b : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (q : Tuning) {a D : ℝ}
    (he : Chart.coefficients q=edgeCoefficients (Chart.rationalCosine j k)
      (Chart.rationalHeight j k) a D) (ha : singletonRoof K j k b D<a) :
    RegularSingletonAt j k hf.1 (Chart.fraction_window_arithmetic hK hf).2.le q ∧
      Threshold.sigma q=0 := by
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  have hbinv := inverse_mod_value (by omega : 3≤k) hb
  obtain ⟨C,hC⟩ := (Ray.aF_lt_iff (by omega) hjk hbinv
    (LargeCurvature.sourceCertificate_nonempty hK hf b hb0 hbk hb D)).mp
      ((le_max_right _ _).trans_lt ha)
  let E := C.edgeCertificate (by omega) hjk hb0 hbk hbinv q he hC
  refine ⟨⟨k,E.regularData,?_⟩,E.sigma_eq⟩
  change Set.range (fun _ : Fin 1=>Edge.atom j k hf.1 hjk.le)={Edge.atom j k hf.1 hjk.le}
  exact Set.range_const

theorem singleton_iff_roof {K j k : ℕ} (hK : 2≤K) (hf : Chart.FractionInWindow K j k)
    (b : ℤ) (hb0 : 0<b) (hbk : b<k) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (q : Tuning) :
    RegularSingletonAt j k hf.1 (Chart.fraction_window_arithmetic hK hf).2.le q ↔
      ∃a D : ℝ,Chart.coefficients q=edgeCoefficients (Chart.rationalCosine j k)
        (Chart.rationalHeight j k) a D ∧ singletonRoof K j k b D<a := by
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  have hk : 3≤k := by omega
  have hbinv := inverse_mod_value hk hb
  constructor
  · rintro ⟨L,R,hS⟩
    have hphase := Edge.singleton_phase_eq R hk (by omega) hjk b hbinv hS
    have hp : q.angle (Regions.rationalAngle j k)=Real.pi/k := by
      rw [Geometry.shiftedCurve_zero] at hphase
      change q.angle (Edge.atom j k _ _)=_ at hphase
      rw [Ray.source_atom_value] at hphase
      exact hphase
    obtain ⟨a,D,_ha0,he,hgap⟩ := source_edge_recovery q hK hf hp
    refine ⟨a,D,he,max_lt_iff.mpr ⟨?_,?_⟩⟩
    · exact hgap.mp (fraction_regular_singleton_gap R hK hf b hbinv hS)
    · exact regular_singleton_aF_lt R hk (by omega) hjk b hb0 hbk hb hS he
  · rintro ⟨a,D,he,ha⟩
    exact (singleton_of_roof hK hf b hb0 hbk hb q he ha).1

end polyak.FareyPlateau
