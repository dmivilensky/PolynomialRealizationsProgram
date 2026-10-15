import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch009
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence009
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence009.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock9` feeds
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
theorem valid288 : ValidPanel panel288 := ⟨check288,ContactValues.valid288⟩
theorem valid289 : ValidPanel panel289 := ⟨check289,ContactValues.valid289⟩
theorem valid290 : ValidPanel panel290 := ⟨check290,ContactValues.valid290⟩
theorem valid291 : ValidPanel panel291 := ⟨check291,ContactValues.valid291⟩
theorem valid292 : ValidPanel panel292 := ⟨check292,ContactValues.valid292⟩
theorem valid293 : ValidPanel panel293 := ⟨check293,ContactValues.valid293⟩
theorem valid294 : ValidPanel panel294 := ⟨check294,ContactValues.valid294⟩
theorem valid295 : ValidPanel panel295 := ⟨check295,ContactValues.valid295⟩
theorem valid296 : ValidPanel panel296 := ⟨check296,ContactValues.valid296⟩
theorem valid297 : ValidPanel panel297 := ⟨check297,ContactValues.valid297⟩
theorem valid298 : ValidPanel panel298 := ⟨check298,ContactValues.valid298⟩
theorem valid299 : ValidPanel panel299 := ⟨check299,ContactValues.valid299⟩
theorem valid300 : ValidPanel panel300 := ⟨check300,ContactValues.valid300⟩
theorem valid301 : ValidPanel panel301 := ⟨check301,ContactValues.valid301⟩
theorem valid302 : ValidPanel panel302 := ⟨check302,ContactValues.valid302⟩
theorem valid303 : ValidPanel panel303 := ⟨check303,ContactValues.valid303⟩
theorem valid304 : ValidPanel panel304 := ⟨check304,ContactValues.valid304⟩
theorem valid305 : ValidPanel panel305 := ⟨check305,ContactValues.valid305⟩
theorem valid306 : ValidPanel panel306 := ⟨check306,ContactValues.valid306⟩
theorem valid307 : ValidPanel panel307 := ⟨check307,ContactValues.valid307⟩
theorem valid308 : ValidPanel panel308 := ⟨check308,ContactValues.valid308⟩
theorem valid309 : ValidPanel panel309 := ⟨check309,ContactValues.valid309⟩
theorem valid310 : ValidPanel panel310 := ⟨check310,ContactValues.valid310⟩
theorem valid311 : ValidPanel panel311 := ⟨check311,ContactValues.valid311⟩
theorem valid312 : ValidPanel panel312 := ⟨check312,ContactValues.valid312⟩
theorem valid313 : ValidPanel panel313 := ⟨check313,ContactValues.valid313⟩
theorem valid314 : ValidPanel panel314 := ⟨check314,ContactValues.valid314⟩
theorem valid315 : ValidPanel panel315 := ⟨check315,ContactValues.valid315⟩
theorem valid316 : ValidPanel panel316 := ⟨check316,ContactValues.valid316⟩
theorem valid317 : ValidPanel panel317 := ⟨check317,ContactValues.valid317⟩
theorem valid318 : ValidPanel panel318 := ⟨check318,ContactValues.valid318⟩
theorem valid319 : ValidPanel panel319 := ⟨check319,ContactValues.valid319⟩
theorem validBlock9 : ∀ p∈block9,ValidPanel p := by
  simp only [block9,List.forall_mem_cons]
  exact ⟨valid288,⟨valid289,⟨valid290,⟨valid291,⟨valid292,⟨valid293,⟨valid294,⟨valid295,⟨valid296,⟨valid297,⟨valid298,⟨valid299,⟨valid300,⟨valid301,⟨valid302,⟨valid303,⟨valid304,⟨valid305,⟨valid306,⟨valid307,⟨valid308,⟨valid309,⟨valid310,⟨valid311,⟨valid312,⟨valid313,⟨valid314,⟨valid315,⟨valid316,⟨valid317,⟨valid318,⟨valid319,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues
