import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch031
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence031
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence031.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock31` feeds
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
theorem valid992 : ValidPanel panel992 := ⟨check992,ContactValues.valid992⟩
theorem valid993 : ValidPanel panel993 := ⟨check993,ContactValues.valid993⟩
theorem valid994 : ValidPanel panel994 := ⟨check994,ContactValues.valid994⟩
theorem valid995 : ValidPanel panel995 := ⟨check995,ContactValues.valid995⟩
theorem valid996 : ValidPanel panel996 := ⟨check996,ContactValues.valid996⟩
theorem valid997 : ValidPanel panel997 := ⟨check997,ContactValues.valid997⟩
theorem valid998 : ValidPanel panel998 := ⟨check998,ContactValues.valid998⟩
theorem valid999 : ValidPanel panel999 := ⟨check999,ContactValues.valid999⟩
theorem valid1000 : ValidPanel panel1000 := ⟨check1000,ContactValues.valid1000⟩
theorem valid1001 : ValidPanel panel1001 := ⟨check1001,ContactValues.valid1001⟩
theorem valid1002 : ValidPanel panel1002 := ⟨check1002,ContactValues.valid1002⟩
theorem valid1003 : ValidPanel panel1003 := ⟨check1003,ContactValues.valid1003⟩
theorem valid1004 : ValidPanel panel1004 := ⟨check1004,ContactValues.valid1004⟩
theorem valid1005 : ValidPanel panel1005 := ⟨check1005,ContactValues.valid1005⟩
theorem valid1006 : ValidPanel panel1006 := ⟨check1006,ContactValues.valid1006⟩
theorem valid1007 : ValidPanel panel1007 := ⟨check1007,ContactValues.valid1007⟩
theorem valid1008 : ValidPanel panel1008 := ⟨check1008,ContactValues.valid1008⟩
theorem valid1009 : ValidPanel panel1009 := ⟨check1009,ContactValues.valid1009⟩
theorem valid1010 : ValidPanel panel1010 := ⟨check1010,ContactValues.valid1010⟩
theorem valid1011 : ValidPanel panel1011 := ⟨check1011,ContactValues.valid1011⟩
theorem valid1012 : ValidPanel panel1012 := ⟨check1012,ContactValues.valid1012⟩
theorem valid1013 : ValidPanel panel1013 := ⟨check1013,ContactValues.valid1013⟩
theorem valid1014 : ValidPanel panel1014 := ⟨check1014,ContactValues.valid1014⟩
theorem valid1015 : ValidPanel panel1015 := ⟨check1015,ContactValues.valid1015⟩
theorem valid1016 : ValidPanel panel1016 := ⟨check1016,ContactValues.valid1016⟩
theorem valid1017 : ValidPanel panel1017 := ⟨check1017,ContactValues.valid1017⟩
theorem valid1018 : ValidPanel panel1018 := ⟨check1018,ContactValues.valid1018⟩
theorem valid1019 : ValidPanel panel1019 := ⟨check1019,ContactValues.valid1019⟩
theorem valid1020 : ValidPanel panel1020 := ⟨check1020,ContactValues.valid1020⟩
theorem valid1021 : ValidPanel panel1021 := ⟨check1021,ContactValues.valid1021⟩
theorem valid1022 : ValidPanel panel1022 := ⟨check1022,ContactValues.valid1022⟩
theorem valid1023 : ValidPanel panel1023 := ⟨check1023,ContactValues.valid1023⟩
theorem validBlock31 : ∀ p∈block31,ValidPanel p := by
  simp only [block31,List.forall_mem_cons]
  exact ⟨valid992,⟨valid993,⟨valid994,⟨valid995,⟨valid996,⟨valid997,⟨valid998,⟨valid999,⟨valid1000,⟨valid1001,⟨valid1002,⟨valid1003,⟨valid1004,⟨valid1005,⟨valid1006,⟨valid1007,⟨valid1008,⟨valid1009,⟨valid1010,⟨valid1011,⟨valid1012,⟨valid1013,⟨valid1014,⟨valid1015,⟨valid1016,⟨valid1017,⟨valid1018,⟨valid1019,⟨valid1020,⟨valid1021,⟨valid1022,⟨valid1023,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues
