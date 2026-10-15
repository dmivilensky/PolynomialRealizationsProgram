import «2610.05164v2».Certificates.Compact.AmplitudeBatches.Batch010
import «2610.05164v2».Certificates.Compact.ContactBatches.Correspondence010
import «2610.05164v2».Certificates.Compact.AmplitudeProof

/-!
Article: 2610.05164v2, Section 4.1.
Correspondence010.
Use: `«2610.05164v2».Certificates.Compact.AmplitudeValues.validBlock10` feeds
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
theorem valid320 : ValidPanel panel320 := ⟨check320,ContactValues.valid320⟩
theorem valid321 : ValidPanel panel321 := ⟨check321,ContactValues.valid321⟩
theorem valid322 : ValidPanel panel322 := ⟨check322,ContactValues.valid322⟩
theorem valid323 : ValidPanel panel323 := ⟨check323,ContactValues.valid323⟩
theorem valid324 : ValidPanel panel324 := ⟨check324,ContactValues.valid324⟩
theorem valid325 : ValidPanel panel325 := ⟨check325,ContactValues.valid325⟩
theorem valid326 : ValidPanel panel326 := ⟨check326,ContactValues.valid326⟩
theorem valid327 : ValidPanel panel327 := ⟨check327,ContactValues.valid327⟩
theorem valid328 : ValidPanel panel328 := ⟨check328,ContactValues.valid328⟩
theorem valid329 : ValidPanel panel329 := ⟨check329,ContactValues.valid329⟩
theorem valid330 : ValidPanel panel330 := ⟨check330,ContactValues.valid330⟩
theorem valid331 : ValidPanel panel331 := ⟨check331,ContactValues.valid331⟩
theorem valid332 : ValidPanel panel332 := ⟨check332,ContactValues.valid332⟩
theorem valid333 : ValidPanel panel333 := ⟨check333,ContactValues.valid333⟩
theorem valid334 : ValidPanel panel334 := ⟨check334,ContactValues.valid334⟩
theorem valid335 : ValidPanel panel335 := ⟨check335,ContactValues.valid335⟩
theorem valid336 : ValidPanel panel336 := ⟨check336,ContactValues.valid336⟩
theorem valid337 : ValidPanel panel337 := ⟨check337,ContactValues.valid337⟩
theorem valid338 : ValidPanel panel338 := ⟨check338,ContactValues.valid338⟩
theorem valid339 : ValidPanel panel339 := ⟨check339,ContactValues.valid339⟩
theorem valid340 : ValidPanel panel340 := ⟨check340,ContactValues.valid340⟩
theorem valid341 : ValidPanel panel341 := ⟨check341,ContactValues.valid341⟩
theorem valid342 : ValidPanel panel342 := ⟨check342,ContactValues.valid342⟩
theorem valid343 : ValidPanel panel343 := ⟨check343,ContactValues.valid343⟩
theorem valid344 : ValidPanel panel344 := ⟨check344,ContactValues.valid344⟩
theorem valid345 : ValidPanel panel345 := ⟨check345,ContactValues.valid345⟩
theorem valid346 : ValidPanel panel346 := ⟨check346,ContactValues.valid346⟩
theorem valid347 : ValidPanel panel347 := ⟨check347,ContactValues.valid347⟩
theorem valid348 : ValidPanel panel348 := ⟨check348,ContactValues.valid348⟩
theorem valid349 : ValidPanel panel349 := ⟨check349,ContactValues.valid349⟩
theorem valid350 : ValidPanel panel350 := ⟨check350,ContactValues.valid350⟩
theorem valid351 : ValidPanel panel351 := ⟨check351,ContactValues.valid351⟩
theorem validBlock10 : ∀ p∈block10,ValidPanel p := by
  simp only [block10,List.forall_mem_cons]
  exact ⟨valid320,⟨valid321,⟨valid322,⟨valid323,⟨valid324,⟨valid325,⟨valid326,⟨valid327,⟨valid328,⟨valid329,⟨valid330,⟨valid331,⟨valid332,⟨valid333,⟨valid334,⟨valid335,⟨valid336,⟨valid337,⟨valid338,⟨valid339,⟨valid340,⟨valid341,⟨valid342,⟨valid343,⟨valid344,⟨valid345,⟨valid346,⟨valid347,⟨valid348,⟨valid349,⟨valid350,⟨valid351,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end «2610.05164v2».Certificates.Compact.AmplitudeValues
