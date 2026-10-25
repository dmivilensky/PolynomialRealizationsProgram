import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic

/-!
Article: first part, equations (abg), (feasible), and Appendix A, Lemma vmono.
Use: probability spectra in the cosine coordinate, with independent twist and exponent.
Proof: continuous polynomial moments make all averaging and parameter dependence explicit.
Source: mathlib probability measures, Chebyshev identities, and Bochner integral.
-/

open MeasureTheory
open scoped Topology

noncomputable section

namespace polyak.Spectral

/-- Article: cosine frequency coordinate. Use: compact carrier of spectra. -/
abbrev Frequency := Set.Icc (-1 : ℝ) 1

/-- Article: spectrum. Use: normalized nonnegative mixtures, including nonatomic ones. -/
abbrev Spectrum := ProbabilityMeasure Frequency

/-- Article: Chebyshev first kind. Use: lag cosine polynomial, with natural indexing. -/
def chebT (n : ℕ) (c : ℝ) : ℝ := (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval c

/-- Article: Chebyshev second kind. Use: lag sine polynomial, also at lag zero. -/
def chebU (n : ℕ) (c : ℝ) : ℝ := (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval c

/-- Article: barred quantities. Use: exact integration with respect to a spectrum. -/
def avg (ν : Spectrum) (f : Frequency → ℝ) : ℝ := ∫ c, f c ∂ν

/-- Article: g=1-c²-u². Use: minimizer slack integrand in the coordinate u=sinh v. -/
def g (u c : ℝ) : ℝ := 1 - c ^ 2 - u ^ 2

/-- Article: Tₙ(cosh t)-Tₙ(c). Use: nonnegative multiplier of g. -/
def lagD (t : ℝ) (n : ℕ) (c : ℝ) : ℝ := Real.cosh (n * t) - chebT n c

/-- Article: aₙ. Use: symmetric part of the lag interpolation inequality. -/
def lagA (u t : ℝ) (n : ℕ) (c : ℝ) : ℝ := g u c * lagD t n c

/-- Article: bₙ. Use: skew part of the lag interpolation inequality. -/
def lagB (u : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  2 * u * (1 - c ^ 2) * chebU (n - 1) c

/-- Article: barred g. Use: algebraic moment representation for compactness. -/
def meanG (ν : Spectrum) (u : ℝ) : ℝ := 1 - avg ν (fun c => (c : ℝ) ^ 2) - u ^ 2

/-- Article: barred aₙ. Use: a finite-moment representation, proved equal to the integral. -/
def meanA (ν : Spectrum) (u t : ℝ) (n : ℕ) : ℝ :=
  Real.cosh (n * t) * meanG ν u -
    avg ν (fun c => (1 - (c : ℝ) ^ 2) * chebT n c) +
    u ^ 2 * avg ν (fun c => chebT n c)

/-- Article: barred bₙ. Use: a finite-moment representation, proved equal to the integral. -/
def meanB (ν : Spectrum) (u : ℝ) (n : ℕ) : ℝ :=
  2 * u * avg ν (fun c => (1 - (c : ℝ) ^ 2) * chebU (n - 1) c)

/-- Article: feasible pair. Use: exact infinite family, with no finite-lag truncation. -/
def FeasibleU (u t : ℝ) (ν : Spectrum) (C : ℝ) : Prop :=
  |C| ≤ meanG ν u ∧ ∀ n : ℕ, 1 ≤ n →
    0 ≤ meanA ν u t n - meanB ν u n + C * Real.sinh (n * t) ∧
    0 ≤ meanA ν u t n + meanB ν u n - C * Real.sinh (n * t)

/-- Article: independent parameters (v,t). Use: the twist coordinate of the paper. -/
def Feasible (v t : ℝ) (ν : Spectrum) (C : ℝ) : Prop := FeasibleU (Real.sinh v) t ν C

/-- Article: polynomial cosine formula. Proof: mathlib's integer-index Chebyshev identity. -/
theorem chebT_cos (n : ℕ) (ω : ℝ) : chebT n (Real.cos ω) = Real.cos (n * ω) := by
  simp [chebT]

/-- Article: polynomial sine formula. Proof: use the division-free identity at all frequencies. -/
theorem chebU_sin (n : ℕ) (ω : ℝ) :
    chebU n (Real.cos ω) * Real.sin ω = Real.sin ((n + 1) * ω) := by
  simp [chebU]

/-- Article: Tₙ(cosh t)=cosh(nt). Proof: hyperbolic Chebyshev identity. -/
theorem chebT_cosh (n : ℕ) (t : ℝ) : chebT n (Real.cosh t) = Real.cosh (n * t) := by
  simp [chebT]

/-- Article: lag nonnegativity. Proof: c=cos(arccos c) and |cos|≤1≤cosh. -/
theorem lagD_nonneg (t : ℝ) (n : ℕ) (c : Frequency) : 0 ≤ lagD t n c := by
  have h : chebT n c ≤ 1 := by
    rw [← Real.cos_arccos c.property.1 c.property.2, chebT_cos]
    exact Real.cos_le_one _
  exact sub_nonneg.mpr (h.trans (Real.one_le_cosh _))

/-- Article: continuous integrands. Use: all required real moments exist. -/
theorem continuous_chebT (n : ℕ) : Continuous (chebT n) :=
  Polynomial.continuous _

/-- Article: continuous integrands. Use: all required real moments exist. -/
theorem continuous_chebU (n : ℕ) : Continuous (chebU n) :=
  Polynomial.continuous _

/-- Article: barred quantities are finite. Proof: continuous functions on a compact carrier. -/
theorem integrable_continuous (ν : Spectrum) {f : Frequency → ℝ} (hf : Continuous f) :
    Integrable f (ν : Measure Frequency) := hf.integrable_of_hasCompactSupport
  (HasCompactSupport.of_compactSpace f)

/-- Article: probability normalization. Use: integration of scalar constants. -/
@[simp] theorem avg_const (ν : Spectrum) (a : ℝ) : avg ν (fun _ => a) = a := by
  simp [avg]

/-- Article: moment representation of g. Proof: linearity of the integral. -/
theorem meanG_eq_integral (ν : Spectrum) (u : ℝ) :
    meanG ν u = avg ν (fun c => g u c) := by
  have hi : Integrable (fun c : Frequency => (c : ℝ) ^ 2) (ν : Measure Frequency) :=
    integrable_continuous ν (by fun_prop)
  have hone : Integrable (fun _ : Frequency => (1 : ℝ)) (ν : Measure Frequency) :=
    integrable_const _
  have hu : Integrable (fun _ : Frequency => u ^ 2) (ν : Measure Frequency) :=
    integrable_const _
  unfold meanG avg g
  dsimp only
  have hs := integral_sub (hone.sub hi) hu
  dsimp only [Pi.sub_apply] at hs
  rw [hs, integral_sub hone hi]
  simp

/-- Article: moment representation of aₙ. Proof: expand the polynomial product under the integral. -/
theorem meanA_eq_integral (ν : Spectrum) (u t : ℝ) (n : ℕ) :
    meanA ν u t n = avg ν (fun c => lagA u t n c) := by
  have hT : Continuous (fun c : Frequency => chebT n c) :=
    (continuous_chebT n).comp continuous_subtype_val
  have h2 : Continuous (fun c : Frequency => (c : ℝ) ^ 2) := by fun_prop
  have heq : (fun c : Frequency => lagA u t n c) =
      (fun c : Frequency => Real.cosh (n * t) * g u c -
        (1 - (c : ℝ) ^ 2) * chebT n c + u ^ 2 * chebT n c) := by
    funext c
    dsimp [lagA, lagD, g]
    ring
  rw [heq]
  have hg := integrable_continuous ν (show Continuous (fun c : Frequency => g u c) by
    unfold g; fun_prop)
  have hw := integrable_continuous ν (((continuous_const : Continuous (fun _ : Frequency => (1 : ℝ))).sub h2).mul hT)
  have ht := integrable_continuous ν hT
  unfold avg
  dsimp only
  have hs := integral_add ((hg.const_mul (Real.cosh (n * t))).sub hw)
    (ht.const_mul (u ^ 2))
  dsimp only [Pi.sub_apply, Pi.mul_apply] at hs
  rw [hs]
  have hs2 := integral_sub (hg.const_mul (Real.cosh (n * t))) hw
  dsimp only [Pi.mul_apply, Pi.sub_apply] at hs2
  rw [hs2]
  simp only [integral_const_mul]
  change meanA ν u t n = Real.cosh (n * t) * avg ν (fun c => g u c) - _ + _
  rw [← meanG_eq_integral]
  rfl

/-- Article: moment representation of bₙ. Proof: scalar linearity of the integral. -/
theorem meanB_eq_integral (ν : Spectrum) (u : ℝ) (n : ℕ) :
    meanB ν u n = avg ν (fun c => lagB u n c) := by
  simp only [meanB, avg, lagB, mul_assoc, integral_const_mul]

/-- Article: minimizer slack bounds C. Proof: g≤1 pointwise. -/
theorem meanG_le_one (ν : Spectrum) (u : ℝ) : meanG ν u ≤ 1 := by
  have h : 0 ≤ avg ν (fun c => (c : ℝ) ^ 2) := integral_nonneg (fun _ => sq_nonneg _)
  dsimp [meanG]
  nlinarith [sq_nonneg u]

/-- Article: compactness lemma. Proof: the minimizer inequality bounds the value parameter. -/
theorem FeasibleU.abs_C_le_one {u t C : ℝ} {ν : Spectrum} (h : FeasibleU u t ν C) :
    |C| ≤ 1 := h.1.trans (meanG_le_one ν u)

/-- Article: |sinh v|≤1. Proof: integrate g and use nonnegativity of the second moment. -/
theorem FeasibleU.abs_u_le_one {u t C : ℝ} {ν : Spectrum} (h : FeasibleU u t ν C) :
    |u| ≤ 1 := by
  have h0 := (abs_nonneg C).trans h.1
  have h2 : 0 ≤ avg ν (fun c => (c : ℝ) ^ 2) := integral_nonneg (fun _ => sq_nonneg _)
  have hu2 : u ^ 2 ≤ 1 := by dsimp [meanG] at h0; linarith
  exact (sq_le_one_iff_abs_le_one u).mp hu2

/-- Article: V≤arsinh 1. Proof: sinh is an order isomorphism. -/
theorem Feasible.abs_v_le_arsinh_one {v t C : ℝ} {ν : Spectrum} (h : Feasible v t ν C) :
    |v| ≤ Real.arsinh 1 := by
  have hu := h.abs_u_le_one
  rw [abs_le] at hu ⊢
  constructor
  · have := (Real.sinh_le_sinh).mp (show Real.sinh (-Real.arsinh 1) ≤ Real.sinh v by
      simpa using hu.1)
    exact this
  · exact (Real.sinh_le_sinh).mp (by simpa using hu.2)

/-- Article: t symmetry. Proof: cosh is even and sinh is odd; the constant changes sign. -/
theorem feasibleU_neg_t_iff (u t C : ℝ) (ν : Spectrum) :
    FeasibleU u (-t) ν (-C) ↔ FeasibleU u t ν C := by
  simp only [FeasibleU, abs_neg, meanA, mul_neg, Real.cosh_neg, Real.sinh_neg, neg_mul,
    mul_neg, neg_neg]

/-- Article: v symmetry. Proof: u² is even while bₙ is odd; the two lag slacks swap. -/
theorem feasibleU_neg_u_iff (u t C : ℝ) (ν : Spectrum) :
    FeasibleU (-u) t ν (-C) ↔ FeasibleU u t ν C := by
  simp only [FeasibleU, abs_neg, meanG, neg_sq, meanA, meanB, mul_neg, neg_mul,
    sub_neg_eq_add]
  constructor <;> rintro ⟨hC, h⟩ <;> refine ⟨hC, fun n hn => ?_⟩ <;>
    obtain ⟨h₁, h₂⟩ := h n hn <;> constructor <;> linarith

/-- Article: symmetries in the original twist variable. Proof: sinh(-v)=-sinh(v). -/
theorem feasible_neg_v_iff (v t C : ℝ) (ν : Spectrum) :
    Feasible (-v) t ν (-C) ↔ Feasible v t ν C := by
  simpa [Feasible] using feasibleU_neg_u_iff (Real.sinh v) t C ν

/-- Article: symmetries in the original exponent variable. Proof: the u statement. -/
theorem feasible_neg_t_iff (v t C : ℝ) (ν : Spectrum) :
    Feasible v (-t) ν (-C) ↔ Feasible v t ν C := feasibleU_neg_t_iff _ _ _ _



/-- Article: averaged nonnegative lag factor. Use: monotonicity without pointwise g≥0. -/
def meanD (ν : Spectrum) (t : ℝ) (n : ℕ) : ℝ :=
  Real.cosh (n * t) - avg ν (fun c => chebT n c)

/-- Article: monotonicity proof. Proof: the Chebyshev lag factor is nonnegative. -/
theorem meanD_nonneg (ν : Spectrum) (t : ℝ) (n : ℕ) : 0 ≤ meanD ν t n := by
  have hT := integrable_continuous ν ((continuous_chebT n).comp continuous_subtype_val)
  have h : avg ν (fun c => chebT n c) ≤ Real.cosh (n * t) := by
    calc
      _ ≤ avg ν (fun _ => Real.cosh (n * t)) := integral_mono hT (integrable_const _)
        (fun c => sub_nonneg.mp (lagD_nonneg t n c))
      _ = _ := avg_const _ _
  exact sub_nonneg.mpr h

/-- Article: scaling of skew slacks. Proof: b is linear in the twist u. -/
theorem meanB_mul (ν : Spectrum) (θ u : ℝ) (n : ℕ) :
    meanB ν (θ * u) n = θ * meanB ν u n := by
  unfold meanB
  ring

/-- Article: change in symmetric slacks. Proof: expand the quadratic twist dependence. -/
theorem meanA_mul (ν : Spectrum) (θ u t : ℝ) (n : ℕ) :
    meanA ν (θ * u) t n = meanA ν u t n +
      (u ^ 2 - (θ * u) ^ 2) * meanD ν t n := by
  unfold meanA meanG meanD
  ring

/-- Article: mean a is nonnegative for feasible data. Proof: add the lower and upper slacks. -/
theorem FeasibleU.meanA_nonneg {u t C : ℝ} {ν : Spectrum} (h : FeasibleU u t ν C)
    (n : ℕ) (hn : 1 ≤ n) : 0 ≤ meanA ν u t n := by
  obtain ⟨hl, hu⟩ := h.2 n hn
  linarith

/-- Article: Lemma vmono(iii), division-free form. Use: includes zero twist.
Proof: new slack = θ old slack +(1-θ) old a + a increment. -/
theorem FeasibleU.scale {u t C θ : ℝ} {ν : Spectrum} (h : FeasibleU u t ν C)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : FeasibleU (θ * u) t ν (θ * C) := by
  have hθsq : θ ^ 2 ≤ 1 := by nlinarith
  have hsq : (θ * u) ^ 2 ≤ u ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hθsq (sq_nonneg u)]
  have hG : meanG ν u ≤ meanG ν (θ * u) := by unfold meanG; linarith
  refine ⟨?_, fun n hn => ?_⟩
  · rw [abs_mul, abs_of_nonneg hθ0]
    exact (mul_le_of_le_one_left (abs_nonneg C) hθ1).trans (h.1.trans hG)
  · have ha := h.meanA_nonneg n hn
    have hinc := mul_nonneg (sub_nonneg.mpr hsq) (meanD_nonneg ν t n)
    have had := mul_nonneg (sub_nonneg.mpr hθ1) ha
    obtain ⟨hl, hu⟩ := h.2 n hn
    have hls := mul_nonneg hθ0 hl
    have hus := mul_nonneg hθ0 hu
    rw [meanA_mul, meanB_mul]
    constructor <;> nlinarith

/-- Article: monotonicity in nonnegative u. Proof: scale by u'/u; zero is a separate case. -/
theorem FeasibleU.mono {u u' t C : ℝ} {ν : Spectrum} (h : FeasibleU u t ν C)
    (hu' : 0 ≤ u') (hu'u : u' ≤ u) : ∃ C', FeasibleU u' t ν C' := by
  by_cases hu : u = 0
  · have hu'0 : u' = 0 := le_antisymm (by simpa [hu] using hu'u) hu'
    exact ⟨C, by simpa [hu, hu'0] using h⟩
  · have hu0 : 0 < u := lt_of_le_of_ne (hu'.trans hu'u) (Ne.symm hu)
    have hs := h.scale (div_nonneg hu' hu0.le) ((div_le_one hu0).mpr hu'u)
    exact ⟨(u' / u) * C, by simpa [div_mul_cancel₀ _ hu] using hs⟩

/-- Article: Lemma vmono(iii) in the original coordinate. Proof: monotonicity of sinh. -/
theorem Feasible.mono {v v' t C : ℝ} {ν : Spectrum} (h : Feasible v t ν C)
    (hv' : 0 ≤ v') (hv'v : v' ≤ v) : ∃ C', Feasible v' t ν C' :=
  FeasibleU.mono h (by simpa using (Real.sinh_le_sinh.mpr hv')) (Real.sinh_le_sinh.mpr hv'v)

end polyak.Spectral
