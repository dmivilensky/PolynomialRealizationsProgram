import chebyshev2.Certificates.DualInputs.Reference
import chebyshev2.DualCertificate.RationalReference

/-!
Article: chebyshev2, Section 4.1.
Positive rational reference data shared by the actual ODE and calibration.
Use: `chebyshev2.Certificates.DualInputs.reference_signs` feeds
`chebyshev2.Certificates.Compact.ContactValues.contact_integral_enclosed` (contact integral
enclosed).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Certificates.DualInputs
open chebyshev2.DualCertificate
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 0

def reference : RationalReference where
  count := 5
  p₀ := Reference.values[5]?.getD 0
  p i := Reference.values[6+2*i.val]?.getD 0
  ζ i := Reference.values[7+2*i.val]?.getD 0
  p₀_pos := by decide +kernel
  p_pos := by intro i; fin_cases i <;> decide +kernel
  ζ_pos := by intro i; fin_cases i <;> decide +kernel

def sigma : ℚ := Reference.values[1]?.getD 0
def base : ℚ := Reference.values[2]?.getD 0
def omega : ℚ := Reference.values[3]?.getD 0
theorem reference_signs : 0<sigma ∧ 0<base ∧ 0≤omega := by decide +kernel
end chebyshev2.Certificates.DualInputs
