import jacobi.Trichotomy.SubcriticalTail
import jacobi.Trichotomy.CriticalTail

/-!
Article: jacobi, Proposition C.4.
The genuine source density is positive precisely on its actual packing
image. Its topological support is therefore that image's closure.
The proved three coordinate regimes give exactly the printed full-line
versus finite-centered-interval classification.
Use: infinite_packedDensity_support gives the full-line branch of Proposition C.4; the finite branch is subcritical_packedDensity_support.
-/
namespace jacobi.Trichotomy
noncomputable section
open Real Set jacobi.Reference

/-- The true topological support of the original packed density is exactly the closure of its actual intrinsic coordinate image.
Use: infinite_packedDensity_support gives the full-line branch of Proposition C.4; the finite branch is subcritical_packedDensity_support.
Article: jacobi, Proposition C.4.
Proof: the actual density is nonnegative, and its proved strict positivity set is precisely the original coordinate image. Its nonzero support equals that same image, so taking the closure gives the topological support. -/
theorem packedDensity_support (a : ℝ) (ha : -1<a) :
    tsupport (packedDensity a ha)=closure (packingImage a ha) := by
  -- The support identity retains every genuine interior point and excludes every zero-extension point.
  change closure (Function.support (packedDensity a ha))=_
  congr 1
  ext x
  constructor
  · intro hx
    exact (packedDensity_pos_iff a ha x).mp
      (lt_of_le_of_ne (packedDensity_nonneg a ha x) (Ne.symm hx))
  · intro hx
    exact ((packedDensity_pos_iff a ha x).mpr hx).ne'

/-- The actual packed persymmetric density has the entire real line as its topological support for every alpha>=-1/2.
Use: completes Proposition C.4's support classification together with the genuine finite-interval theorem below the critical order.
Article: jacobi, Proposition C.4.
Proof: the genuine critical and supercritical coordinate images have each been proved to be the whole real line, from their actual divergent endpoint asymptotics. The general actual support identity gives the same full-line support. -/
theorem infinite_packedDensity_support {a : ℝ} (ha : -1<a) (hs : -(1/2:ℝ)≤a) :
    tsupport (packedDensity a ha)=univ := by
  rw [packedDensity_support]
  have hfull : packingImage a ha=univ := by
    rcases eq_or_lt_of_le hs with h | h
    · subst a
      exact critical_packingImage ha
    · exact supercritical_packingImage ha h
  rw [hfull,closure_univ]

end
end jacobi.Trichotomy
