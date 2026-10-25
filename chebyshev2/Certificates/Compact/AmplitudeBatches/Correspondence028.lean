import chebyshev2.Certificates.Compact.AmplitudeBatches.Batch028
import chebyshev2.Certificates.Compact.ContactBatches.Correspondence028
import chebyshev2.Certificates.Compact.AmplitudeProof

/-!
Article: chebyshev2, Section 4.1.
Correspondence028.
Use: `chebyshev2.Certificates.Compact.AmplitudeValues.validBlock28` feeds
`chebyshev2.Certificates.Compact.AmplitudeValues.all_valid` (all valid).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace chebyshev2.Certificates.Compact.AmplitudeValues
open chebyshev2.Numerics.IntegerCertificate
theorem valid896 : ValidPanel panel896 := ⟨check896,ContactValues.valid896⟩
theorem valid897 : ValidPanel panel897 := ⟨check897,ContactValues.valid897⟩
theorem valid898 : ValidPanel panel898 := ⟨check898,ContactValues.valid898⟩
theorem valid899 : ValidPanel panel899 := ⟨check899,ContactValues.valid899⟩
theorem valid900 : ValidPanel panel900 := ⟨check900,ContactValues.valid900⟩
theorem valid901 : ValidPanel panel901 := ⟨check901,ContactValues.valid901⟩
theorem valid902 : ValidPanel panel902 := ⟨check902,ContactValues.valid902⟩
theorem valid903 : ValidPanel panel903 := ⟨check903,ContactValues.valid903⟩
theorem valid904 : ValidPanel panel904 := ⟨check904,ContactValues.valid904⟩
theorem valid905 : ValidPanel panel905 := ⟨check905,ContactValues.valid905⟩
theorem valid906 : ValidPanel panel906 := ⟨check906,ContactValues.valid906⟩
theorem valid907 : ValidPanel panel907 := ⟨check907,ContactValues.valid907⟩
theorem valid908 : ValidPanel panel908 := ⟨check908,ContactValues.valid908⟩
theorem valid909 : ValidPanel panel909 := ⟨check909,ContactValues.valid909⟩
theorem valid910 : ValidPanel panel910 := ⟨check910,ContactValues.valid910⟩
theorem valid911 : ValidPanel panel911 := ⟨check911,ContactValues.valid911⟩
theorem valid912 : ValidPanel panel912 := ⟨check912,ContactValues.valid912⟩
theorem valid913 : ValidPanel panel913 := ⟨check913,ContactValues.valid913⟩
theorem valid914 : ValidPanel panel914 := ⟨check914,ContactValues.valid914⟩
theorem valid915 : ValidPanel panel915 := ⟨check915,ContactValues.valid915⟩
theorem valid916 : ValidPanel panel916 := ⟨check916,ContactValues.valid916⟩
theorem valid917 : ValidPanel panel917 := ⟨check917,ContactValues.valid917⟩
theorem valid918 : ValidPanel panel918 := ⟨check918,ContactValues.valid918⟩
theorem valid919 : ValidPanel panel919 := ⟨check919,ContactValues.valid919⟩
theorem valid920 : ValidPanel panel920 := ⟨check920,ContactValues.valid920⟩
theorem valid921 : ValidPanel panel921 := ⟨check921,ContactValues.valid921⟩
theorem valid922 : ValidPanel panel922 := ⟨check922,ContactValues.valid922⟩
theorem valid923 : ValidPanel panel923 := ⟨check923,ContactValues.valid923⟩
theorem valid924 : ValidPanel panel924 := ⟨check924,ContactValues.valid924⟩
theorem valid925 : ValidPanel panel925 := ⟨check925,ContactValues.valid925⟩
theorem valid926 : ValidPanel panel926 := ⟨check926,ContactValues.valid926⟩
theorem valid927 : ValidPanel panel927 := ⟨check927,ContactValues.valid927⟩
theorem validBlock28 : ∀ p∈block28,ValidPanel p := by
  simp only [block28,List.forall_mem_cons]
  exact ⟨valid896,⟨valid897,⟨valid898,⟨valid899,⟨valid900,⟨valid901,⟨valid902,⟨valid903,⟨valid904,⟨valid905,⟨valid906,⟨valid907,⟨valid908,⟨valid909,⟨valid910,⟨valid911,⟨valid912,⟨valid913,⟨valid914,⟨valid915,⟨valid916,⟨valid917,⟨valid918,⟨valid919,⟨valid920,⟨valid921,⟨valid922,⟨valid923,⟨valid924,⟨valid925,⟨valid926,⟨valid927,(by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end chebyshev2.Certificates.Compact.AmplitudeValues
