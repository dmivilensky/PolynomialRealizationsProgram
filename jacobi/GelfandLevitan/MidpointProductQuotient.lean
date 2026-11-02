import jacobi.GelfandLevitan.SeparatedSimplicity
import jacobi.Complex.SimpleZeroQuotient
import jacobi.Reference.CharacteristicBessel

/-!
Article: jacobi, Proposition C.2.
The actual product of the two separated midpoint characteristics and
the original Delta_sigma have exactly the same simple complex zeros.
Their genuine quotient therefore extends to an entire zero-free
function. The further growth argument must prove that this actual
quotient is constant before the printed characteristic identity follows.
Use: midpointProductQuotient compares its complete simple zero set with the original full Bessel characteristic before boundary identification.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
set_option backward.isDefEq.respectTransparency false

/-- The product of the actual two original separated midpoint characteristics.
Use: midpointProductQuotient compares its complete simple zero set with the original full Bessel characteristic before boundary identification.
Article: jacobi, Proposition C.2.
-/
def separatedProduct (a : ℝ) (ha : -1<a) (z : ℂ) : ℂ :=
  separatedCharacteristic a ha 0 z*separatedCharacteristic a ha 1 z

/-- The two actual original separated characteristics have no common complex zero.
Use: separatedProduct_simple retains multiplicity one when the original parity spectra are united.
Article: jacobi, Proposition C.2.
Proof: a common zero would equal sigma_(2*i) and sigma_(2*j+1). Strict monotonicity of the original sigma list forces equal indices, contradicting their different parity. -/
theorem separatedCharacteristics_no_common_zero (a : ℝ) (ha : -1<a) {z : ℂ}
    (h0 : separatedCharacteristic a ha 0 z=0) : separatedCharacteristic a ha 1 z≠0 := by
  intro h1
  obtain ⟨i,hi⟩ := (separatedCharacteristic_zero_iff a ha 0 z).mp h0
  obtain ⟨j,hj⟩ := (separatedCharacteristic_zero_iff a ha 1 z).mp h1
  have he := (jacobi.Bessel.sigma_strictMono ha).injective (Complex.ofReal_injective (hi.symm.trans hj))
  change 2*i+0=2*j+1 at he
  omega

/-- The original two separated characteristic classes together have exactly the unchanged full Bessel characteristic zero set.
Use: midpointProductQuotient_analytic removes every actual denominator zero with the original multiplicity retained.
Article: jacobi, Proposition C.2.
Proof: use the exhaustive proved complex zero sets in each class and the exhaustive original Delta_sigma zero set. Euclidean even/odd division assigns every original index to one of the two actual classes. -/
theorem separatedProduct_zero_iff (a : ℝ) (ha : -1<a) (z : ℂ) :
    separatedProduct a ha z=0 ↔ characteristicSigma a z=0 := by
  -- Both implications concern the original entire functions, including arbitrary nonreal energies.
  rw [separatedProduct,mul_eq_zero,characteristicSigma_zero_iff ha]
  constructor
  · intro h
    rcases h with h|h
    · obtain ⟨k,hk⟩ := (separatedCharacteristic_zero_iff a ha 0 z).mp h
      exact ⟨parityIndex 0 k,hk⟩
    · obtain ⟨k,hk⟩ := (separatedCharacteristic_zero_iff a ha 1 z).mp h
      exact ⟨parityIndex 1 k,hk⟩
  · rintro ⟨k,rfl⟩
    obtain ⟨n,hn|hn⟩ := Nat.even_or_odd' k
    · left
      have he : k=parityIndex 0 n := by simpa only [parityIndex,Fin.val_zero,Nat.add_zero] using hn
      rw [he]
      exact separatedCharacteristic_at_spectrum a ha 0 n
    · right
      have he : k=parityIndex 1 n := hn
      rw [he]
      exact separatedCharacteristic_at_spectrum a ha 1 n

/-- The actual separated product is entire in the original energy variable.
Use: midpointProductQuotient_analytic extends the actual quotient over all original spectral zeros.
Article: jacobi, Proposition C.2.
Proof: multiply the independently proved genuine entire separated characteristics. -/
theorem separatedProduct_analytic (a : ℝ) (ha : -1<a) (z : ℂ) :
    AnalyticAt ℂ (separatedProduct a ha) z :=
  (separatedCharacteristic_analytic a ha 0 z).mul (separatedCharacteristic_analytic a ha 1 z)

/-- Every original complex zero of the actual product of separated characteristics is simple.
Use: midpointProductQuotient_ne_zero verifies genuine multiplicity preservation in the characteristic comparison.
Article: jacobi, Proposition C.2.
Proof: exactly one actual separated characteristic vanishes at a product zero. Its genuine derivative is nonzero by the proved Green norm identity; the product rule multiplies it by the nonzero other characteristic. -/
theorem separatedProduct_simple (a : ℝ) (ha : -1<a) {z : ℂ}
    (hz : separatedProduct a ha z=0) : deriv (separatedProduct a ha) z≠0 := by
  -- Disjoint original parity zero sets ensure that the product rule retains exactly one nonzero simple-zero derivative term.
  have hd := ((separatedCharacteristic_analytic a ha 0 z).differentiableAt.hasDerivAt.mul
    (separatedCharacteristic_analytic a ha 1 z).differentiableAt.hasDerivAt).deriv
  change deriv (separatedProduct a ha) z=_ at hd
  rw [hd]
  rcases mul_eq_zero.mp hz with h0|h1
  · rw [h0,zero_mul,add_zero]
    exact mul_ne_zero (separatedCharacteristic_simple a ha 0 h0) (separatedCharacteristics_no_common_zero a ha h0)
  · have h0 : separatedCharacteristic a ha 0 z≠0 := fun h => separatedCharacteristics_no_common_zero a ha h h1
    rw [h1,mul_zero,zero_add]
    exact mul_ne_zero h0 (separatedCharacteristic_simple a ha 1 h1)

/-- The actual original characteristic comparison, with the uniquely removable derivative values at every genuine target zero.
Use: its entire, zero-free extension is the original function whose growth must determine the normalization in the midpoint product identity.
Article: jacobi, Proposition C.2.
-/
def midpointProductQuotient (a : ℝ) (ha : -1<a) : ℂ → ℂ :=
  jacobi.Complex.simpleZeroQuotient (separatedProduct a ha) (characteristicSigma a)

/-- The actual original separated-product quotient is entire across every original spectral zero.
Use: the growth comparison for the exact midpoint characteristic identity applies to this genuine entire function, with all removable-singularity premises discharged.
Article: jacobi, Proposition C.2.
Proof: the two original zero sets agree and every original Delta_sigma zero is independently proved simple. Apply analytic divided-difference division to the original entire functions. -/
theorem midpointProductQuotient_analytic (a : ℝ) (ha : -1<a) (z : ℂ) :
    AnalyticAt ℂ (midpointProductQuotient a ha) z :=
  jacobi.Complex.simpleZeroQuotient_analytic (separatedProduct_analytic a ha z)
    (characteristicSigma_analytic a z) (fun hz =>
      ⟨(separatedProduct_zero_iff a ha z).mpr hz,characteristicSigma_simple ha hz⟩)

/-- The true entire quotient gives a global exact factorization of the original separated product, including all original spectral zeros.
Use: once its constancy is established by growth, this same identity supplies the fully normalized midpoint characteristic product.
Article: jacobi, Proposition C.2.
Proof: the actual removable quotient multiplies back to its original numerator, since all original denominator zeros are genuine common zeros. -/
theorem midpointProductQuotient_factor (a : ℝ) (ha : -1<a) (z : ℂ) :
    midpointProductQuotient a ha z*characteristicSigma a z=separatedProduct a ha z :=
  jacobi.Complex.simpleZeroQuotient_mul (fun w hw => (separatedProduct_zero_iff a ha w).mpr hw) z

/-- The actual entire original separated-product quotient is nowhere zero.
Use: the full characteristic growth comparison retains exactly the original simple target spectrum with no hidden extra entire zero factor.
Article: jacobi, Proposition C.2.
Proof: both genuine full characteristic zero sets agree and both functions have independently proved simple zeros; their actual removable derivative ratios are therefore nonzero as well. -/
theorem midpointProductQuotient_ne_zero (a : ℝ) (ha : -1<a) (z : ℂ) :
    midpointProductQuotient a ha z≠0 :=
  jacobi.Complex.simpleZeroQuotient_ne_zero (separatedProduct_zero_iff a ha)
    (fun _ hz => separatedProduct_simple a ha hz) (fun _ hz => characteristicSigma_simple ha hz) z

end
end jacobi.GelfandLevitan
