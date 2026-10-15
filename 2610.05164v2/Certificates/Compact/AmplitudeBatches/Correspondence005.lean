import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch005
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence005
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence005.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock5` feeds
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
theorem valid160 : ValidPanel panel160 := ⟨check160,ContactValues.valid160⟩
theorem valid161 : ValidPanel panel161 := ⟨check161,ContactValues.valid161⟩
theorem valid162 : ValidPanel panel162 := ⟨check162,ContactValues.valid162⟩
theorem valid163 : ValidPanel panel163 := ⟨check163,ContactValues.valid163⟩
theorem valid164 : ValidPanel panel164 := ⟨check164,ContactValues.valid164⟩
theorem valid165 : ValidPanel panel165 := ⟨check165,ContactValues.valid165⟩
theorem valid166 : ValidPanel panel166 := ⟨check166,ContactValues.valid166⟩
theorem valid167 : ValidPanel panel167 := ⟨check167,ContactValues.valid167⟩
theorem valid168 : ValidPanel panel168 := ⟨check168,ContactValues.valid168⟩
theorem valid169 : ValidPanel panel169 := ⟨check169,ContactValues.valid169⟩
theorem valid170 : ValidPanel panel170 := ⟨check170,ContactValues.valid170⟩
theorem valid171 : ValidPanel panel171 := ⟨check171,ContactValues.valid171⟩
theorem valid172 : ValidPanel panel172 := ⟨check172,ContactValues.valid172⟩
theorem valid173 : ValidPanel panel173 := ⟨check173,ContactValues.valid173⟩
theorem valid174 : ValidPanel panel174 := ⟨check174,ContactValues.valid174⟩
theorem valid175 : ValidPanel panel175 := ⟨check175,ContactValues.valid175⟩
theorem valid176 : ValidPanel panel176 := ⟨check176,ContactValues.valid176⟩
theorem valid177 : ValidPanel panel177 := ⟨check177,ContactValues.valid177⟩
theorem valid178 : ValidPanel panel178 := ⟨check178,ContactValues.valid178⟩
theorem valid179 : ValidPanel panel179 := ⟨check179,ContactValues.valid179⟩
theorem valid180 : ValidPanel panel180 := ⟨check180,ContactValues.valid180⟩
theorem valid181 : ValidPanel panel181 := ⟨check181,ContactValues.valid181⟩
theorem valid182 : ValidPanel panel182 := ⟨check182,ContactValues.valid182⟩
theorem valid183 : ValidPanel panel183 := ⟨check183,ContactValues.valid183⟩
theorem valid184 : ValidPanel panel184 := ⟨check184,ContactValues.valid184⟩
theorem valid185 : ValidPanel panel185 := ⟨check185,ContactValues.valid185⟩
theorem valid186 : ValidPanel panel186 := ⟨check186,ContactValues.valid186⟩
theorem valid187 : ValidPanel panel187 := ⟨check187,ContactValues.valid187⟩
theorem valid188 : ValidPanel panel188 := ⟨check188,ContactValues.valid188⟩
theorem valid189 : ValidPanel panel189 := ⟨check189,ContactValues.valid189⟩
theorem valid190 : ValidPanel panel190 := ⟨check190,ContactValues.valid190⟩
theorem valid191 : ValidPanel panel191 := ⟨check191,ContactValues.valid191⟩
theorem validBlock5 : ∀ p∈block5,ValidPanel p := by
  simp only [block5,List.forall_mem_cons]
  exact ⟨valid160,⟨valid161,⟨valid162,⟨valid163,⟨valid164,⟨valid165,⟨valid166,⟨valid167,⟨valid168,⟨valid169,⟨valid170,⟨valid171,⟨valid172,⟨valid173,⟨valid174,⟨valid175,⟨valid176,⟨valid177,⟨valid178,⟨valid179,⟨valid180,⟨valid181,⟨valid182,⟨valid183,⟨valid184,⟨valid185,⟨valid186,⟨valid187,⟨valid188,⟨valid189,⟨valid190,⟨valid191,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues
