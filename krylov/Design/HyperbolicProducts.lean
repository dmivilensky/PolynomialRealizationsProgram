import krylov.Design.AlternatingSechConvolution
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
Article: main_krylov, apC:lem:poisson, genuine hyperbolic products for the nome bridge.
Use: express the product of the actual alternating and ordinary integer sech
sums as the actual alternating squared-sech sum. This proves the first key
elliptic duplication product by actual absolutely convergent convolutions.
Source: the independently proved alternating orthogonality and unconditional
integer-series rearrangement; no theta or elliptic identity is assumed.
-/

namespace krylov.Design
noncomputable section
open Real Filter jacobi.Young

/-- Actual absolutely convergent integer-series multiplication has the genuine convolution form.
Article: main_krylov, apC:lem:poisson. -/
theorem tsum_integer_convolution (f g : ℤ → ℝ) (hf : Summable f) (hg : Summable g) :
    (∑' n : ℤ, f n) * (∑' n : ℤ, g n) = ∑' k : ℤ, ∑' n : ℤ, f n * g (k - n) := by
  let e : (ℤ × ℤ) ≃ (ℤ × ℤ) :=
    { toFun := fun p => (p.2, p.1 - p.2)
      invFun := fun p => (p.1 + p.2, p.1)
      left_inv := by intro p; ext <;> simp
      right_inv := by intro p; ext <;> simp }
  have hs := summable_mul_of_summable_norm hf.norm hg.norm
  have he : Summable (fun p : ℤ × ℤ => f p.2 * g (p.1 - p.2)) := by
    simpa only [Function.comp_def, e] using! hs.comp_injective e.injective
  rw [tsum_mul_tsum_of_summable_norm hf.norm hg.norm, ← e.tsum_eq (fun p : ℤ × ℤ => f p.1 * g p.2)]
  exact he.tsum_prod

/-- Multiplication by the actual integer alternating character preserves absolute summability.
Article: main_krylov, apC:lem:poisson. -/
theorem alternating_integer_summable (f : ℤ → ℝ) (hf : Summable f) :
    Summable (fun n : ℤ => (-1 : ℝ) ^ n * f n) := by
  apply hf.norm.of_norm_bounded
  intro n
  rw [norm_mul, Real.norm_eq_abs, abs_neg_one_zpow, one_mul]

/-- The actual even-lattice projection of any absolutely convergent integer series.
Article: main_krylov, apC:lem:poisson, the arithmetic half of duplication. -/
theorem tsum_integer_even_projection (f : ℤ → ℝ) (hf : Summable f) :
    (∑' n : ℤ, f n) + (∑' n : ℤ, (-1 : ℝ) ^ n * f n) =
      2 * ∑' n : ℤ, f (2 * n) := by
  have ha := alternating_integer_summable f hf
  rw [← hf.tsum_add ha, tsum_integer_even_odd _ (hf.add ha), ← tsum_mul_left]
  apply tsum_congr
  intro n
  have he : (-1 : ℝ) ^ (2 * n) = 1 := Even.neg_one_zpow ⟨n, by ring⟩
  have ho : (-1 : ℝ) ^ (2 * n + 1) = -1 := Odd.neg_one_zpow ⟨n, by ring⟩
  rw [he, ho]
  ring

/-- The genuine ordinary integer sech mass.
Article: main_krylov, apC:lem:poisson, A(theta) in the AGM proof. -/
def latticeSechMass (θ : ℝ) : ℝ := ∑' n : ℤ, sech ((n : ℝ) * θ)

/-- The genuine alternating integer sech mass.
Article: main_krylov, apC:lem:poisson, B(theta) in the AGM proof. -/
def latticeSechAlternatingMass (θ : ℝ) : ℝ := ∑' n : ℤ, (-1 : ℝ) ^ n * sech ((n : ℝ) * θ)

/-- The genuine integer squared-sech mass.
Article: main_krylov, apC:lem:poisson. -/
def latticeSechSquaredMass (θ : ℝ) : ℝ := ∑' n : ℤ, sech ((n : ℝ) * θ) ^ 2

/-- The genuine alternating integer squared-sech mass.
Article: main_krylov, apC:lem:poisson. -/
def latticeSechSquaredAlternatingMass (θ : ℝ) : ℝ :=
  ∑' n : ℤ, (-1 : ℝ) ^ n * sech ((n : ℝ) * θ) ^ 2

/-- The actual integer squared-sech mass is absolutely summable.
Article: main_krylov, apC:lem:poisson. -/
theorem sechSquared_integer_summable {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℤ => sech ((n : ℝ) * θ) ^ 2) := by
  convert! sech_integer_product_summable hθ 0 using 1
  funext n
  simp only [zero_sub, Int.cast_neg, neg_mul, sech_neg, pow_two]

/-- The actual ordinary and alternating integer sech masses obey the arithmetic duplication identity.
Article: main_krylov, apC:lem:poisson, the first actual AGM coordinate. -/
theorem latticeSechMass_duplication {θ : ℝ} (hθ : 0 < θ) :
    latticeSechMass (2 * θ) = (latticeSechMass θ + latticeSechAlternatingMass θ) / 2 := by
  have h := tsum_integer_even_projection (fun n : ℤ => sech ((n : ℝ) * θ)) (sech_integer_summable hθ)
  have he : (∑' n : ℤ, sech (((2 * n : ℤ) : ℝ) * θ)) = latticeSechMass (2 * θ) := by
    apply tsum_congr
    intro n
    rw [show ((2 * n : ℤ) : ℝ) * θ = (n : ℝ) * (2 * θ) by push_cast; ring]
  rw [he] at h
  simp only [latticeSechMass, latticeSechAlternatingMass] at h ⊢
  linarith

/-- The actual alternating square mass is the genuine even projection of the ordinary square mass.
Article: main_krylov, apC:lem:poisson, an exact parity identity. -/
theorem latticeSechSquaredAlternatingMass_eq {θ : ℝ} (hθ : 0 < θ) :
    latticeSechSquaredAlternatingMass θ = 2 * latticeSechSquaredMass (2 * θ) - latticeSechSquaredMass θ := by
  have h := tsum_integer_even_projection (fun n : ℤ => sech ((n : ℝ) * θ) ^ 2)
    (sechSquared_integer_summable hθ)
  have he : (∑' n : ℤ, sech (((2 * n : ℤ) : ℝ) * θ) ^ 2) = latticeSechSquaredMass (2 * θ) := by
    apply tsum_congr
    intro n
    rw [show ((2 * n : ℤ) : ℝ) * θ = (n : ℝ) * (2 * θ) by push_cast; ring]
  rw [he] at h
  simp only [latticeSechSquaredAlternatingMass, latticeSechSquaredMass] at h ⊢
  linarith

/-- The actual ordinary-times-alternating secant product equals the actual alternating square sum.
Article: main_krylov, apC:lem:poisson, the first genuine elliptic duplication product.
Proof: actual product convolution, independently proved zero nonzero-shift
alternating correlations, and the literal zero correlation. -/
theorem latticeSechMass_mul_alternating {θ : ℝ} (hθ : 0 < θ) :
    latticeSechMass θ * latticeSechAlternatingMass θ = latticeSechSquaredAlternatingMass θ := by
  unfold latticeSechMass latticeSechAlternatingMass latticeSechSquaredAlternatingMass
  rw [mul_comm, tsum_integer_convolution _ _
    (alternating_integer_summable _ (sech_integer_summable hθ)) (sech_integer_summable hθ)]
  simp_rw [mul_assoc]
  rw [tsum_eq_single 0 (fun k hk => alternating_sech_convolution hθ hk)]
  apply tsum_congr
  intro n
  simp only [zero_sub, Int.cast_neg, neg_mul, sech_neg, pow_two]

end
end krylov.Design
