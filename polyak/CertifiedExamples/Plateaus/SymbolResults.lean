import polyak.Certificates.PartII.Plateaus.SymbolChecks

/-! Accepted global dual-polynomial certificates for both selected plateaus.
The only inputs are the actual parameter/dual enclosures and exact contact
zero jets, supplied by the algebraic determinant construction. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open LeanCert.Core General Set
open polyak.Certificates.PartII.Plateaus

theorem row18_global_polynomial (q:Tuning) (lam:Fin 4→ℝ) (c:Fin 2→ℝ)
    (hX:∀i,coefficientVector q i∈row18Xi i)
    (hlam:∀j,lam j∈row18DualBoxes j) (hC:∀i,c i∈row18Cosines i)
    (hzero:∀i,indexedSymbol q row18Lags lam (c i)=0)
    (hslope:∀i,deriv (indexedSymbol q row18Lags lam) (c i)=0)
    {x:ℝ} (hx:x∈Icc (-1:ℝ) 1) (hne:∀i,x≠c i) : indexedSymbol q row18Lags lam x<0 :=
  cover_strict q row18Lags lam row18Xi row18DualBoxes row18Cosines c
    row18Family0 row18Family2 21 row18Cover row18Family0_identity row18Family2_identity
    row18Cover_checked hX hlam hC hzero hslope hx hne

theorem row18_polynomial_curvature (q:Tuning) (lam:Fin 4→ℝ) (c:Fin 2→ℝ)
    (hX:∀i,coefficientVector q i∈row18Xi i)
    (hlam:∀j,lam j∈row18DualBoxes j) (hC:∀i,c i∈row18Cosines i) (i:Fin 2) :
    deriv^[2] (indexedSymbol q row18Lags lam) (c i)<0 :=
  cover_curvature q row18Lags lam row18Xi row18DualBoxes row18Cosines c
    row18Family0 row18Family2 21 row18Cover row18Family2_identity row18Cover_checked hX hlam hC i

theorem row21_global_polynomial (q:Tuning) (lam:Fin 6→ℝ) (c:Fin 3→ℝ)
    (hX:∀i,coefficientVector q i∈row21Xi i)
    (hlam:∀j,lam j∈row21DualBoxes j) (hC:∀i,c i∈row21Cosines i)
    (hzero:∀i,indexedSymbol q row21Lags lam (c i)=0)
    (hslope:∀i,deriv (indexedSymbol q row21Lags lam) (c i)=0)
    {x:ℝ} (hx:x∈Icc (-1:ℝ) 1) (hne:∀i,x≠c i) : indexedSymbol q row21Lags lam x<0 :=
  cover_strict q row21Lags lam row21Xi row21DualBoxes row21Cosines c
    row21Family0 row21Family2 27 row21Cover row21Family0_identity row21Family2_identity
    row21Cover_checked hX hlam hC hzero hslope hx hne

theorem row21_polynomial_curvature (q:Tuning) (lam:Fin 6→ℝ) (c:Fin 3→ℝ)
    (hX:∀i,coefficientVector q i∈row21Xi i)
    (hlam:∀j,lam j∈row21DualBoxes j) (hC:∀i,c i∈row21Cosines i) (i:Fin 3) :
    deriv^[2] (indexedSymbol q row21Lags lam) (c i)<0 :=
  cover_curvature q row21Lags lam row21Xi row21DualBoxes row21Cosines c
    row21Family0 row21Family2 27 row21Cover row21Family2_identity row21Cover_checked hX hlam hC i

end polyak.CertifiedExamples.Plateaus
