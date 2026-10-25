import polyak.Certificates.PartII.Plateaus.CoefficientChecks

/-! Actual Xi membership and original gap membership throughout both isolating
kappa brackets. These statements retain every real kappa in the interval. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels
open polyak.Certificates.PartII.Plateaus

theorem row18_Xi_mem (q:Tuning) (hy:q.y=2201327/1000000) (hb:q.beta=1567/2500)
    (hk:q.kappa∈row18Kappa) : ∀i,coefficientVector q i∈row18Xi i := by
  apply Xi_mem_of_checks q row18Y row18Beta row18Kappa row18Xi
    (by simpa [row18Y] using hy) (by simpa [row18Beta] using hb) hk row18_coefficients_checked

theorem row21_Xi_mem (q:Tuning) (hy:q.y=89631/40000) (hb:q.beta=769/1250)
    (hk:q.kappa∈row21Kappa) : ∀i,coefficientVector q i∈row21Xi i := by
  apply Xi_mem_of_checks q row21Y row21Beta row21Kappa row21Xi
    (by simpa [row21Y] using hy) (by simpa [row21Beta] using hb) hk row21_coefficients_checked

theorem row18_in_gap_four (q:Tuning) (hy:q.y=2201327/1000000) (hb:q.beta=1567/2500)
    (hk:q.kappa∈row18Kappa) : Geometry.Gap 4 q :=
  gap_four_of_checked_boxes q row18Xi (row18_Xi_mem q hy hb hk) row18_gap_checked

theorem row21_in_gap_four (q:Tuning) (hy:q.y=89631/40000) (hb:q.beta=769/1250)
    (hk:q.kappa∈row21Kappa) : Geometry.Gap 4 q :=
  gap_four_of_checked_boxes q row21Xi (row21_Xi_mem q hy hb hk) row21_gap_checked

end polyak.CertifiedExamples.Plateaus
