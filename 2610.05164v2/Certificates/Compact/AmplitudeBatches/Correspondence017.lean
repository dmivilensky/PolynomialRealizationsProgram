import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch017
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence017
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence017.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock17` feeds
`«2610.05164v2».Certificates.Compact.AmplitudeValues.all_valid` (all valid).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace «2610.05164v2».Certificates.Compact.AmplitudeValues
open «2610.05164v2».Numerics.IntegerCertificate
theorem valid544 : ValidPanel panel544 := ⟨check544,ContactValues.valid544⟩
theorem valid545 : ValidPanel panel545 := ⟨check545,ContactValues.valid545⟩
theorem valid546 : ValidPanel panel546 := ⟨check546,ContactValues.valid546⟩
theorem valid547 : ValidPanel panel547 := ⟨check547,ContactValues.valid547⟩
theorem valid548 : ValidPanel panel548 := ⟨check548,ContactValues.valid548⟩
theorem valid549 : ValidPanel panel549 := ⟨check549,ContactValues.valid549⟩
theorem valid550 : ValidPanel panel550 := ⟨check550,ContactValues.valid550⟩
theorem valid551 : ValidPanel panel551 := ⟨check551,ContactValues.valid551⟩
theorem valid552 : ValidPanel panel552 := ⟨check552,ContactValues.valid552⟩
theorem valid553 : ValidPanel panel553 := ⟨check553,ContactValues.valid553⟩
theorem valid554 : ValidPanel panel554 := ⟨check554,ContactValues.valid554⟩
theorem valid555 : ValidPanel panel555 := ⟨check555,ContactValues.valid555⟩
theorem valid556 : ValidPanel panel556 := ⟨check556,ContactValues.valid556⟩
theorem valid557 : ValidPanel panel557 := ⟨check557,ContactValues.valid557⟩
theorem valid558 : ValidPanel panel558 := ⟨check558,ContactValues.valid558⟩
theorem valid559 : ValidPanel panel559 := ⟨check559,ContactValues.valid559⟩
theorem valid560 : ValidPanel panel560 := ⟨check560,ContactValues.valid560⟩
theorem valid561 : ValidPanel panel561 := ⟨check561,ContactValues.valid561⟩
theorem valid562 : ValidPanel panel562 := ⟨check562,ContactValues.valid562⟩
theorem valid563 : ValidPanel panel563 := ⟨check563,ContactValues.valid563⟩
theorem valid564 : ValidPanel panel564 := ⟨check564,ContactValues.valid564⟩
theorem valid565 : ValidPanel panel565 := ⟨check565,ContactValues.valid565⟩
theorem valid566 : ValidPanel panel566 := ⟨check566,ContactValues.valid566⟩
theorem valid567 : ValidPanel panel567 := ⟨check567,ContactValues.valid567⟩
theorem valid568 : ValidPanel panel568 := ⟨check568,ContactValues.valid568⟩
theorem valid569 : ValidPanel panel569 := ⟨check569,ContactValues.valid569⟩
theorem valid570 : ValidPanel panel570 := ⟨check570,ContactValues.valid570⟩
theorem valid571 : ValidPanel panel571 := ⟨check571,ContactValues.valid571⟩
theorem valid572 : ValidPanel panel572 := ⟨check572,ContactValues.valid572⟩
theorem valid573 : ValidPanel panel573 := ⟨check573,ContactValues.valid573⟩
theorem valid574 : ValidPanel panel574 := ⟨check574,ContactValues.valid574⟩
theorem valid575 : ValidPanel panel575 := ⟨check575,ContactValues.valid575⟩
theorem validBlock17 : ∀ p∈block17,ValidPanel p := by
  simp only [block17,List.forall_mem_cons]
  exact ⟨valid544,⟨valid545,⟨valid546,⟨valid547,⟨valid548,⟨valid549,⟨valid550,⟨valid551,⟨valid552,⟨valid553,⟨valid554,⟨valid555,⟨valid556,⟨valid557,⟨valid558,⟨valid559,⟨valid560,⟨valid561,⟨valid562,⟨valid563,⟨valid564,⟨valid565,⟨valid566,⟨valid567,⟨valid568,⟨valid569,⟨valid570,⟨valid571,⟨valid572,⟨valid573,⟨valid574,⟨valid575,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues
