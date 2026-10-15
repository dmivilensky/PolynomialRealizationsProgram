import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch002
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence002
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence002.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock2` feeds
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
theorem valid64 : ValidPanel panel64 := ⟨check64,ContactValues.valid64⟩
theorem valid65 : ValidPanel panel65 := ⟨check65,ContactValues.valid65⟩
theorem valid66 : ValidPanel panel66 := ⟨check66,ContactValues.valid66⟩
theorem valid67 : ValidPanel panel67 := ⟨check67,ContactValues.valid67⟩
theorem valid68 : ValidPanel panel68 := ⟨check68,ContactValues.valid68⟩
theorem valid69 : ValidPanel panel69 := ⟨check69,ContactValues.valid69⟩
theorem valid70 : ValidPanel panel70 := ⟨check70,ContactValues.valid70⟩
theorem valid71 : ValidPanel panel71 := ⟨check71,ContactValues.valid71⟩
theorem valid72 : ValidPanel panel72 := ⟨check72,ContactValues.valid72⟩
theorem valid73 : ValidPanel panel73 := ⟨check73,ContactValues.valid73⟩
theorem valid74 : ValidPanel panel74 := ⟨check74,ContactValues.valid74⟩
theorem valid75 : ValidPanel panel75 := ⟨check75,ContactValues.valid75⟩
theorem valid76 : ValidPanel panel76 := ⟨check76,ContactValues.valid76⟩
theorem valid77 : ValidPanel panel77 := ⟨check77,ContactValues.valid77⟩
theorem valid78 : ValidPanel panel78 := ⟨check78,ContactValues.valid78⟩
theorem valid79 : ValidPanel panel79 := ⟨check79,ContactValues.valid79⟩
theorem valid80 : ValidPanel panel80 := ⟨check80,ContactValues.valid80⟩
theorem valid81 : ValidPanel panel81 := ⟨check81,ContactValues.valid81⟩
theorem valid82 : ValidPanel panel82 := ⟨check82,ContactValues.valid82⟩
theorem valid83 : ValidPanel panel83 := ⟨check83,ContactValues.valid83⟩
theorem valid84 : ValidPanel panel84 := ⟨check84,ContactValues.valid84⟩
theorem valid85 : ValidPanel panel85 := ⟨check85,ContactValues.valid85⟩
theorem valid86 : ValidPanel panel86 := ⟨check86,ContactValues.valid86⟩
theorem valid87 : ValidPanel panel87 := ⟨check87,ContactValues.valid87⟩
theorem valid88 : ValidPanel panel88 := ⟨check88,ContactValues.valid88⟩
theorem valid89 : ValidPanel panel89 := ⟨check89,ContactValues.valid89⟩
theorem valid90 : ValidPanel panel90 := ⟨check90,ContactValues.valid90⟩
theorem valid91 : ValidPanel panel91 := ⟨check91,ContactValues.valid91⟩
theorem valid92 : ValidPanel panel92 := ⟨check92,ContactValues.valid92⟩
theorem valid93 : ValidPanel panel93 := ⟨check93,ContactValues.valid93⟩
theorem valid94 : ValidPanel panel94 := ⟨check94,ContactValues.valid94⟩
theorem valid95 : ValidPanel panel95 := ⟨check95,ContactValues.valid95⟩
theorem validBlock2 : ∀ p∈block2,ValidPanel p := by
  simp only [block2,List.forall_mem_cons]
  exact ⟨valid64,⟨valid65,⟨valid66,⟨valid67,⟨valid68,⟨valid69,⟨valid70,⟨valid71,⟨valid72,⟨valid73,⟨valid74,⟨valid75,⟨valid76,⟨valid77,⟨valid78,⟨valid79,⟨valid80,⟨valid81,⟨valid82,⟨valid83,⟨valid84,⟨valid85,⟨valid86,⟨valid87,⟨valid88,⟨valid89,⟨valid90,⟨valid91,⟨valid92,⟨valid93,⟨valid94,⟨valid95,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues
