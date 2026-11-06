import nesterov.Attainment.NormalizedCertificate
import nesterov.Closure.SpectralSet

/-! A genuine zero-charge limiting dual exists at the maximal feasible
exponent. No finite support, active set, or nonzero limiting symbol is assumed. -/
noncomputable section
open Set Filter
open scoped Topology OnePoint
namespace nesterov.Attainment
open Spectral

/-- Compactness retains the charge and the whole complex-frequency symbol
while the actual exponent moves inside a compact interval. -/
theorem exists_limiting_dual_of_sequence (u p : Polynomial ℝ) (lo hi σ : ℝ) (hlo : 0 < lo)
    (s₀ : LagParameter lo hi) (s : ℕ → LagParameter lo hi)
    (hs : Tendsto s atTop (𝓝 s₀))
    (hcert : ∀ n, Nonempty (StrictCertificate (polynomialPair u p (σ*s n)) (s n))) :
    ∃ d ∈ polynomialDualHull u p lo hi σ hlo, d.1=0 ∧
      ∀ c : Frequency, (d.2 (s₀,physicalAngle lo hlo c)).re ≤ 0 := by
  have hx (n : ℕ) : ∃ d ∈ polynomialDualHull u p lo hi σ hlo, d.1=0 ∧
      ∀ c : Frequency, (d.2 (s n,physicalAngle lo hlo c)).re ≤ 0 := by
    obtain ⟨cert⟩ := hcert n
    exact exists_normalized_dual u p lo hi σ hlo (s n) cert
  choose d hd hcharge hneg using hx
  obtain ⟨D,hD,φ,hφ,hlim⟩ :=
    (isCompact_dualHull lo hi hlo (gapEntireMap u p lo hi σ) (skewEntireMap u p lo hi σ)).tendsto_subseq hd
  refine ⟨D,hD,?_,fun c => ?_⟩
  · exact (isClosed_eq continuous_fst continuous_const).mem_of_tendsto hlim
      (Eventually.of_forall (fun n => hcharge (φ n)))
  · have heval : Continuous (fun q : LagParameter lo hi × DualPoint lo hi =>
        q.2.2 (q.1,physicalAngle lo hlo c)) :=
      continuous_eval.comp (continuous_snd.snd.prodMk (continuous_fst.prodMk continuous_const))
    have ht := ((Complex.continuous_re.comp heval).tendsto (s₀,D)).comp
      ((hs.comp hφ.tendsto_atTop).prodMk_nhds hlim)
    exact le_of_tendsto ht (Eventually.of_forall (fun n => hneg (φ n) c))

/-- A compact positive-radius frame for either sign of the physical exponent. -/
structure ExponentFrame (t : ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  sign : ℝ
  sign_cases : sign=1 ∨ sign= -1
  physical : sign*radius=t

namespace ExponentFrame
variable {t : ℝ} (F : ExponentFrame t)

def lo : ℝ := F.radius/2
def hi : ℝ := 3*F.radius/2

def center : LagParameter F.lo F.hi := ⟨F.radius, by
  constructor <;> dsimp [lo,hi] <;> linarith [F.radius_pos]⟩

def offset (n : ℕ) : ℝ := F.radius/(4*((n : ℝ)+1))

theorem offset_pos (n : ℕ) : 0 < F.offset n := by exact div_pos F.radius_pos (by positivity)

theorem offset_le (n : ℕ) : F.offset n ≤ F.radius/4 := by
  dsimp [offset]
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<4*((n:ℝ)+1)) (by norm_num : (0:ℝ)<4)).mpr
  nlinarith [mul_nonneg F.radius_pos.le (Nat.cast_nonneg n)]

def approaching (n : ℕ) : LagParameter F.lo F.hi :=
  ⟨F.radius+F.sign*F.offset n, by
    have hp := F.offset_pos n
    have hb := F.offset_le n
    rcases F.sign_cases with h | h <;> rw [h] <;>
      constructor <;> dsimp [lo,hi] <;> nlinarith [F.radius_pos]⟩

theorem approaching_physical (n : ℕ) : F.sign*(F.approaching n : ℝ) = t+F.offset n := by
  have hsq : F.sign^2=1 := by rcases F.sign_cases with h | h <;> simp [h]
  change F.sign*(F.radius+F.sign*F.offset n)=t+F.offset n
  rw [mul_add, ← mul_assoc, ← pow_two, hsq, one_mul, F.physical]

theorem approaching_tendsto : Tendsto F.approaching atTop (𝓝 F.center) := by
  have hinv : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hn
  have hoff : Tendsto F.offset atTop (𝓝 0) := by
    convert hinv.const_mul (F.radius/4) using 1
    · funext n
      dsimp [offset]
      field_simp
    · simp
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun n => F.radius+F.sign*F.offset n) atTop (𝓝 F.radius)
  simpa only [mul_zero,add_zero] using (hoff.const_mul F.sign).const_add F.radius

end ExponentFrame

theorem exists_exponentFrame {t : ℝ} (ht : t ≠ 0) : Nonempty (ExponentFrame t) := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · exact ⟨⟨-t, neg_pos.mpr ht, -1, Or.inr rfl, by ring⟩⟩
  · exact ⟨⟨t, ht, 1, Or.inl rfl, by ring⟩⟩

theorem frame_strictCertificates (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (F : ExponentFrame (Closure.T M μ L)) :
    ∀ n, Nonempty (StrictCertificate
      (polynomialPair M.queryPolynomial (M.normalizedPolynomial μ L) (F.sign*F.approaching n))
      (F.approaching n)) := by
  intro n
  apply (nesterov.Duality.infeasible_iff_strictCertificate _ _).mp
  rintro ⟨ν,C,h⟩
  have horig : ∃ C', Feasible (M.symbolPair μ L (F.sign*(F.approaching n : ℝ)))
      (F.sign*(F.approaching n : ℝ)) ν C' := by
    rcases F.sign_cases with hs | hs
    · refine ⟨C, ?_⟩
      simpa only [polynomialPair, StationaryMethod.symbolPair, hs,one_mul] using h
    · refine ⟨-C, ?_⟩
      have hh := (feasible_neg_t_iff (M.symbolPair μ L (-(F.approaching n : ℝ)))
        (F.approaching n) C ν).mpr (by
          simpa only [polynomialPair, StationaryMethod.symbolPair, hs,neg_one_mul] using h)
      simpa only [hs,neg_one_mul] using hh
  obtain ⟨C',h'⟩ := horig
  have hmax := (Closure.T_isGreatest M hμ hμL).2
    (show F.sign*(F.approaching n : ℝ) ∈ Closure.spectralSet M μ L from ⟨ν,C',h'⟩)
  rw [F.approaching_physical] at hmax
  exact (not_le_of_gt (lt_add_of_pos_right _ (F.offset_pos n))) hmax


/-- The limiting-certificate assertion for the literal maximal feasible exponent. -/
theorem exists_limiting_dual_at_T (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) (ht : Closure.T M μ L ≠ 0) :
    ∃ F : ExponentFrame (Closure.T M μ L),
      ∃ d ∈ polynomialDualHull M.queryPolynomial (M.normalizedPolynomial μ L) F.lo F.hi F.sign
        (half_pos F.radius_pos), d.1=0 ∧ ∀ c : Frequency,
          (d.2 (F.center,physicalAngle F.lo (half_pos F.radius_pos) c)).re ≤ 0 := by
  obtain ⟨F⟩ := exists_exponentFrame ht
  refine ⟨F, exists_limiting_dual_of_sequence M.queryPolynomial (M.normalizedPolynomial μ L)
    F.lo F.hi F.sign (half_pos F.radius_pos) F.center F.approaching F.approaching_tendsto
      (frame_strictCertificates M hμ hμL F)⟩

end nesterov.Attainment
