import jacobi.Reference.Parameters
import jacobi.Bessel.EdgeData
import jacobi.Complex.EntireUniqueness

/-!
Article: jacobi, Proposition 2.2.
The actual shifted Bessel frequencies are positive, strictly increasing
and bounded above by pi*k plus a fixed constant at every original index.
They therefore satisfy the fully proved entire-function uniqueness
theorem. The positive shift gap is the genuine B5 theorem from.
Use: the original spectral coefficient transform vanishes at both signs of exactly these frequencies in the source GL injectivity argument.
-/
namespace jacobi.Reference
noncomputable section
open Real Set
open scoped Topology

/-- The actual positive Bessel frequency after subtracting the true reference potential shift.
Use: the original spectral coefficient transform vanishes at both signs of exactly these frequencies in the source GL injectivity argument.
Article: jacobi, Proposition C.4.
-/
def besselFrequency (a : ℝ) (ha : -1<a) (k : ℕ) : ℝ :=
  Real.sqrt (jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a)

/-- Every original shifted Bessel frequency is strictly positive, including the first one for every original order.
Use: the actual signed frequency roots are distinct and the zero family has no doubled origin in Jensen's formula.
Article: jacobi, Proposition 2.2.
Proof: the proved genuine B5 shift gap makes the actual square-root argument positive. -/
theorem besselFrequency_pos {a : ℝ} (ha : -1<a) (k : ℕ) : 0<besselFrequency a ha k :=
  Real.sqrt_pos.mpr (sub_pos.mpr (jacobi.Bessel.sigma_above_correction ha k))

/-- The genuine shifted Bessel frequencies have exactly their original squared source energies.
Use: identifies zeros of the actual frequency transform with the genuine Bessel energies without a square-root branch assumption.
Article: jacobi, Proposition 2.2.
Proof: use the actual nonnegative square-root argument, supplied by the proved strict B5 gap. -/
theorem besselFrequency_sq {a : ℝ} (ha : -1<a) (k : ℕ) :
    (besselFrequency a ha k)^2= jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a :=
  Real.sq_sqrt (sub_nonneg.mpr (jacobi.Bessel.sigma_above_correction ha k).le)

/-- The actual shifted Bessel frequency sequence is strictly increasing in its original exhaustive enumeration.
Use: gives the true simple signed zero sequence in source GL completeness, not merely a positive comparison grid.
Article: jacobi, Proposition 2.2.
Proof: the genuine squared Bessel spectrum is strictly increasing, subtracting the common shift preserves its order, and square root is strict above zero. -/
theorem besselFrequency_strictMono {a : ℝ} (ha : -1<a) : StrictMono (besselFrequency a ha) := by
  intro i j hij
  exact Real.sqrt_lt_sqrt (sub_nonneg.mpr (jacobi.Bessel.sigma_above_correction ha i).le)
    (sub_lt_sub_right (jacobi.Bessel.sigma_strictMono ha hij) _)

/-- All actual shifted Bessel frequencies lie below the original pi grid plus one fixed constant, with no omitted small index.
Use: discharges the quantitative root-count input of the fully proved Jensen uniqueness theorem for the genuine source spectrum.
Article: jacobi, Proposition 2.2.
Proof: the true squared spectral displacement is uniformly bounded by
its proved inverse-square McMahon estimate. Add the fixed positive
margin A+1 to the actual positive reference phase; its square dominates
the original shifted Bessel energy. Take the genuine nonnegative roots. -/
theorem besselFrequency_upper {a : ℝ} (ha : -1<a) :
    ∃ D:ℝ,0<D ∧ ∀ k,besselFrequency a ha k≤Real.pi*(k+D) := by
  -- The true constant absorbs the finite original prefix through the already proved all-index McMahon bound.
  obtain ⟨A,hA,hbound⟩ := spectrum_error ha
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  refine ⟨gamma a+(A+1)/Real.pi,by positivity,fun k => ?_⟩
  have hk : (1:ℝ)≤(k+1:ℝ)^2 := by nlinarith [show (0:ℝ)≤k from Nat.cast_nonneg k]
  have hdiv : A/(k+1:ℝ)^2≤A := div_le_self hA.le hk
  have hd : jacobi.Bessel.sigma a ha k-eigenvalue a k≤A :=
    (le_abs_self _).trans ((hbound k).trans hdiv)
  have hphase : 0<Real.pi*(k+gamma a) := by positivity
  have htarget : Real.pi*(k+(gamma a+(A+1)/Real.pi))=Real.pi*(k+gamma a)+A+1 := by
    field_simp
    ring
  rw [htarget]
  have hs := besselFrequency_sq ha k
  have hp := besselFrequency_pos ha k
  dsimp [eigenvalue] at hd
  nlinarith [mul_pos hphase hA]

/-- The actual original shifted Bessel zero set is a uniqueness set for every entire function of the source half-interval exponential type.
Use: completes the analytic uniqueness step for the genuine source GL coefficient transform once its actual integral representation is identified.
Article: jacobi, Proposition 2.2.
Source: Levin, Distribution of Zeros of Entire Functions, Jensen's formula, here proved from the community formula.
Proof: every premise of the fully proved finite-block Jensen theorem is supplied by the actual original Bessel sequence and its genuine shift gap and McMahon estimate. -/
theorem bessel_entire_uniqueness {a : ℝ} (ha : -1<a) {f : ℂ → ℂ}
    (hf : ∀ z,AnalyticAt ℂ f z)
    (hzero : ∀ k,f (besselFrequency a ha k:ℂ)=0 ∧ f (-(besselFrequency a ha k:ℂ))=0)
    (hgrowth : ∃ C:ℝ,0<C ∧ ∀ z,‖f z‖≤C*Real.exp (‖z‖/2)) : f=0 :=
  jacobi.Complex.eq_zero_of_signed_roots_type_half hf (besselFrequency_strictMono ha)
    (besselFrequency_pos ha) (besselFrequency_upper ha) hzero hgrowth

end
end jacobi.Reference
