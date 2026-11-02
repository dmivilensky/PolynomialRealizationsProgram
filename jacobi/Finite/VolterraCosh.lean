import jacobi.Finite.VolterraMajorant
import jacobi.Finite.WeightedVolterraInequality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
The original positive linear Volterra comparison has the genuine
factorial hyperbolic-cosine bound. Exact binomial coefficients replace
the source's separate real-power summations, and the actual complex
weighted equation is connected through the shared norm inequality.
Source: Pascal's identity and the community hyperbolic-cosine series.
Use: linear_volterra_cosh and weighted_volterra_cosh provide the original global energy-scaled support-wave bound.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset

/-- The actual finite positive binomial Volterra majorant is bounded by the genuine hyperbolic-cosine series with its factorial denominators.
Use: linear_volterra_cosh and weighted_volterra_cosh provide the original global energy-scaled support-wave bound.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the community binomial bound gives choose(M+k,2*k)<= (M+k)^(2*k)/(2*k)!. On the actual finite sum k<=M, this is bounded by (2*(M+1))^(2*k)/(2*k)!. The genuine square root of a converts each factor a^k into the even power of the cosh argument; the positive finite sum is at most its actual convergent community series. -/
theorem linear_majorant_cosh (M : ℕ) {a : ℝ} (ha:0≤a) :
    linearMajorant M a M≤cosh (2*sqrt a*((M:ℝ)+1)) := by
  -- Each original finite iterate retains its true factorial; no exponential in the squared energy replaces the printed cosh.
  let T : ℝ := 2*sqrt a*((M:ℝ)+1)
  have hT : 0≤T := by dsimp [T]; positivity
  have hterm : ∀k∈range (M+1),a^k*((M+k).choose (2*k):ℝ)≤T^(2*k)/((2*k).factorial:ℝ) := by
    intro k hk
    have hkM : k≤M := by have := mem_range.mp hk; omega
    have hchoose := Nat.choose_le_pow_div (α:=ℝ) (2*k) (M+k)
    have hidx : ((M+k:ℕ):ℝ)≤2*((M:ℝ)+1) := by push_cast; exact_mod_cast (show M+k≤2*(M+1) by omega)
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (M+k) (α:=ℝ)) hidx (2*k)
    have hfac : 0≤((2*k).factorial:ℝ) := Nat.cast_nonneg _
    have hTpow : T^(2*k)=a^k*(2*((M:ℝ)+1))^(2*k) := by
      dsimp [T]
      rw [show 2*sqrt a*((M:ℝ)+1)=sqrt a*(2*((M:ℝ)+1)) by ring,mul_pow,pow_mul,Real.sq_sqrt ha]
    calc
      _ ≤ a^k*(((M+k:ℕ):ℝ)^(2*k)/((2*k).factorial:ℝ)) := mul_le_mul_of_nonneg_left hchoose (pow_nonneg ha _)
      _ ≤ a^k*((2*((M:ℝ)+1))^(2*k)/((2*k).factorial:ℝ)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow hfac) (pow_nonneg ha _)
      _ = _ := by rw [hTpow]; ring
  calc
    _ ≤ ∑k∈range (M+1),T^(2*k)/((2*k).factorial:ℝ) := sum_le_sum hterm
    _ ≤ ∑'k:ℕ,T^(2*k)/((2*k).factorial:ℝ) :=
      (Real.hasSum_cosh T).summable.sum_le_tsum _ (fun k hk => by positivity)
    _ = _ := (Real.hasSum_cosh T).tsum_eq

/-- Every genuine finite positive linear-kernel triangular inequality has the printed global hyperbolic-cosine bound.
Use: weighted_volterra_cosh applies this to the actual original support-wave norm equation with every kernel hypothesis proved.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: strong finite-prefix comparison bounds the actual original sequence by its exact positive binomial majorant; the proved factorial series bound is the genuine cosh. -/
theorem linear_volterra_cosh {v : ℕ→ℝ} {C a : ℝ} (hC:0≤C) (ha:0≤a) (M : ℕ)
    (hv:∀j≤M,v j≤C+a*∑k∈range j,((j-k:ℕ):ℝ)*v k) :
    v M≤C*cosh (2*sqrt a*((M:ℝ)+1)) :=
  (linear_majorant_bound ha M hv).trans (mul_le_mul_of_nonneg_left (linear_majorant_cosh M ha) hC)

/-- The actual finite complex weighted Volterra equation has the full original global hyperbolic-cosine estimate.
Use: Support.naturalWave_cosh supplies the genuine original support wave, top-node solution, original kernel and positive growth weights, discharging every premise.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the proved genuine complex-to-scalar norm comparison is a positive linear Volterra inequality. Its actual finite binomial majorant has the community cosh bound, and multiplication by the same genuine positive original weight restores the wave norm. -/
theorem weighted_volterra_cosh (u v : ℕ→ℂ) (G : ℕ→ℕ→ℝ) (w : ℕ→ℝ)
    (d : ℂ) (M : ℕ) {C B : ℝ} (hC:0≤C) (hB:0≤B) (hw:∀j≤M,0<w j)
    (hu:∀j≤M,‖u j‖≤C*w j)
    (hG:∀j≤M,∀k<j,0≤G j k ∧ G j k*w k/w j≤B*((j-k:ℕ):ℝ))
    (hv:∀j≤M,v j=u j+d*∑k∈range j,(G j k:ℂ)*v k) :
    ‖v M‖≤C*w M*cosh (2*sqrt (‖d‖*B)*((M:ℝ)+1)) := by
  have h := linear_volterra_cosh hC (mul_nonneg (norm_nonneg d) hB) M
    (weighted_volterra_inequality u v G w d M hw hu hG hv)
  have h' := (div_le_iff₀ (hw M le_rfl)).mp h
  calc
    _ ≤ (C*cosh (2*sqrt (‖d‖*B)*((M:ℝ)+1)))*w M := h'
    _ = _ := by ring

end
end jacobi.Finite
