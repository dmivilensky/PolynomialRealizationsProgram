import polyak.Certificates.PartII.Plateaus.SymbolData

/-! Every source identity and every global Bernstein bound is checked by the ordinary kernel. -/
namespace polyak.Certificates.PartII.Plateaus
open polyak.CertifiedExamples.Plateaus

theorem row18Family0_identity :
    familyIdentityCheck row18Lags 0 row18Family0=true := by kernel_decide

theorem row18Family2_identity :
    familyIdentityCheck row18Lags 2 row18Family2=true := by kernel_decide

theorem row18Cover_checked :
    coverCheck row18Xi row18DualBoxes row18Cosines row18Family0 row18Family2
      21 row18Cover=true := by kernel_decide

theorem row21Family0_identity :
    familyIdentityCheck row21Lags 0 row21Family0=true := by kernel_decide

theorem row21Family2_identity :
    familyIdentityCheck row21Lags 2 row21Family2=true := by kernel_decide

theorem row21Cover_checked :
    coverCheck row21Xi row21DualBoxes row21Cosines row21Family0 row21Family2
      27 row21Cover=true := by kernel_decide

end polyak.Certificates.PartII.Plateaus
