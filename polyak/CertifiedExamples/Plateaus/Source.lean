import polyak.CertifiedExamples.Plateaus.Sites
import polyak.CertifiedExamples.Plateaus.GapBounds
import polyak.CertifiedExamples.Plateaus.Coordinates

/-! Fixed actual tunings, support cosine coordinates and canonical adjugate
kernels for the two certified examples. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels

 def coordinates18 : Fin 2→ℝ:=fun i=>Real.cos (atoms18 i:ℝ)
 def coordinates21 : Fin 3→ℝ:=fun i=>Real.cos (atoms21 i:ℝ)

 def sourceMatrix18 : Matrix (Fin 2) (Fin 2) ℝ :=
   coordinateMatrix (coefficientVector tuning18) ![1,-4] coordinates18
 def sourceMatrix21 : Matrix (Fin 3) (Fin 3) ℝ :=
   coordinateMatrix (coefficientVector tuning21) ![1,-12,-4] coordinates21

 def rho18 : Fin 2→ℝ:=positivePrimal sourceMatrix18 0
 def rho21 : Fin 3→ℝ:=positivePrimal sourceMatrix21 0
 def mu18 : Fin 2→ℝ:=positiveDual sourceMatrix18 0
 def mu21 : Fin 3→ℝ:=positiveDual sourceMatrix21 0

theorem coefficientVector_actual (q:Tuning) (c:ℝ) :
    coefficientValue (coefficientVector q) c=q.Xi c :=
  Chart.eval_coefficients q c

theorem coordinateLag_actual_coefficients (q:Tuning) (n:ℤ) (c:ℝ) :
    coordinateLag (coefficientVector q) n c=Farey.Certificates.signedLagPolynomial q n c := by
  unfold coordinateLag Farey.Certificates.signedLagPolynomial
  rw [coefficientVector_actual]

theorem sourceMatrix18_actual (r i:Fin 2) : sourceMatrix18 r i=
    Farey.Certificates.signedLagPolynomial tuning18 ((![1,-4]:Fin 2→ℤ) r) (coordinates18 i) :=
  coordinateLag_actual_coefficients _ _ _

theorem sourceMatrix21_actual (r i:Fin 3) : sourceMatrix21 r i=
    Farey.Certificates.signedLagPolynomial tuning21 ((![1,-12,-4]:Fin 3→ℤ) r) (coordinates21 i) :=
  coordinateLag_actual_coefficients _ _ _

theorem coordinates18_eq : coordinates18=
    ![Real.cos (2*Real.pi*3/18),Real.cos (2*Real.pi*4/18)] := by
  funext i
  fin_cases i <;> norm_num [coordinates18,atoms18,gridAtom,General.Regions.rationalAngle]

theorem coordinates21_eq : coordinates21=
    ![Real.cos (2*Real.pi*3/21),Real.cos (2*Real.pi*4/21),Real.cos (2*Real.pi*5/21)] := by
  funext i
  fin_cases i <;> norm_num [coordinates21,atoms21,gridAtom,General.Regions.rationalAngle]

end polyak.CertifiedExamples.Plateaus
