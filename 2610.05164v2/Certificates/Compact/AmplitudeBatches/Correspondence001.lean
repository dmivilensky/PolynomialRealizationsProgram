import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch001
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence001
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence001.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock1` feeds
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
theorem valid32 : ValidPanel panel32 := ⟨check32,ContactValues.valid32⟩
theorem valid33 : ValidPanel panel33 := ⟨check33,ContactValues.valid33⟩
theorem valid34 : ValidPanel panel34 := ⟨check34,ContactValues.valid34⟩
theorem valid35 : ValidPanel panel35 := ⟨check35,ContactValues.valid35⟩
theorem valid36 : ValidPanel panel36 := ⟨check36,ContactValues.valid36⟩
theorem valid37 : ValidPanel panel37 := ⟨check37,ContactValues.valid37⟩
theorem valid38 : ValidPanel panel38 := ⟨check38,ContactValues.valid38⟩
theorem valid39 : ValidPanel panel39 := ⟨check39,ContactValues.valid39⟩
theorem valid40 : ValidPanel panel40 := ⟨check40,ContactValues.valid40⟩
theorem valid41 : ValidPanel panel41 := ⟨check41,ContactValues.valid41⟩
theorem valid42 : ValidPanel panel42 := ⟨check42,ContactValues.valid42⟩
theorem valid43 : ValidPanel panel43 := ⟨check43,ContactValues.valid43⟩
theorem valid44 : ValidPanel panel44 := ⟨check44,ContactValues.valid44⟩
theorem valid45 : ValidPanel panel45 := ⟨check45,ContactValues.valid45⟩
theorem valid46 : ValidPanel panel46 := ⟨check46,ContactValues.valid46⟩
theorem valid47 : ValidPanel panel47 := ⟨check47,ContactValues.valid47⟩
theorem valid48 : ValidPanel panel48 := ⟨check48,ContactValues.valid48⟩
theorem valid49 : ValidPanel panel49 := ⟨check49,ContactValues.valid49⟩
theorem valid50 : ValidPanel panel50 := ⟨check50,ContactValues.valid50⟩
theorem valid51 : ValidPanel panel51 := ⟨check51,ContactValues.valid51⟩
theorem valid52 : ValidPanel panel52 := ⟨check52,ContactValues.valid52⟩
theorem valid53 : ValidPanel panel53 := ⟨check53,ContactValues.valid53⟩
theorem valid54 : ValidPanel panel54 := ⟨check54,ContactValues.valid54⟩
theorem valid55 : ValidPanel panel55 := ⟨check55,ContactValues.valid55⟩
theorem valid56 : ValidPanel panel56 := ⟨check56,ContactValues.valid56⟩
theorem valid57 : ValidPanel panel57 := ⟨check57,ContactValues.valid57⟩
theorem valid58 : ValidPanel panel58 := ⟨check58,ContactValues.valid58⟩
theorem valid59 : ValidPanel panel59 := ⟨check59,ContactValues.valid59⟩
theorem valid60 : ValidPanel panel60 := ⟨check60,ContactValues.valid60⟩
theorem valid61 : ValidPanel panel61 := ⟨check61,ContactValues.valid61⟩
theorem valid62 : ValidPanel panel62 := ⟨check62,ContactValues.valid62⟩
theorem valid63 : ValidPanel panel63 := ⟨check63,ContactValues.valid63⟩
theorem validBlock1 : ∀ p∈block1,ValidPanel p := by
  simp only [block1,List.forall_mem_cons]
  exact ⟨valid32,⟨valid33,⟨valid34,⟨valid35,⟨valid36,⟨valid37,⟨valid38,⟨valid39,⟨valid40,⟨valid41,⟨valid42,⟨valid43,⟨valid44,⟨valid45,⟨valid46,⟨valid47,⟨valid48,⟨valid49,⟨valid50,⟨valid51,⟨valid52,⟨valid53,⟨valid54,⟨valid55,⟨valid56,⟨valid57,⟨valid58,⟨valid59,⟨valid60,⟨valid61,⟨valid62,⟨valid63,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues
