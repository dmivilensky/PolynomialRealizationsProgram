import jacobi.Support.FixedWeightLimit
import jacobi.Support.WeightSineProducts
import jacobi.Support.WeightAngleBounds
import jacobi.Support.SineProductBounds
import jacobi.Analysis.ComparablePowers

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
On the right spectral half, the actual support probabilities divided by
the first actual probability grow as (k+1)^(2*gamma_alpha), uniformly in
the full growing index range. Reflection supplies the opposite endpoint.
The proof reuses the complete sine-product estimates and works also when
2*gamma_beta-1 is negative.
Use: supportWeight_bounds combines this quantitative global ratio with the independently proved first weight normalization; these original weights then control the entire spectral tails in the two-edge Gram limit.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference jacobi.Analysis
open scoped Topology

/-- Every actual support probability on the right spectral half has the full original uniform power growth relative to its first probability.
Use: supportWeight_bounds combines this quantitative global ratio with the independently proved first weight normalization; these original weights then control the entire spectral tails in the two-edge Gram limit.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: insert the exact support probability formula in its reflected two-sine-product form. The angular ratio is linear, the alpha product has its proved original power growth, and the beta product ratio stays uniformly bounded because its two lengths differ by at most a factor two. Compare the genuine positive real powers for both signs of the beta exponent and multiply the bounds. -/
theorem supportWeight_ratio_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀k:ℕ,2*k≤n→
      c*((k:ℝ)+1)^(2*gamma a)≤naturalWeight a b ha hb n k/naturalWeight a b ha hb n 0 ∧
      naturalWeight a b ha hb n k/naturalWeight a b ha hb n 0≤C*((k:ℝ)+1)^(2*gamma a) := by
  -- The half-step product theorem covers every length used here, not just fixed spectral indices.
  have hg := parameter_pos ha hb
  obtain ⟨c₀,C₀,hc₀,hC₀,hangle⟩ := weightAngle_ratio_bounds ha hb
  obtain ⟨c₁,C₁,hc₁,hC₁,hA⟩ := support_sineProduct_bounds a b (show 0<2*gamma a by linarith [hg.1])
  obtain ⟨c₂,C₂,hc₂,hC₂,hB⟩ := support_sineProduct_bounds a b (show 0<2*gamma b by linarith [hg.2.1])
  let e : ℝ := 2*gamma b-1
  let l : ℝ := (1/2:ℝ)^|e|
  let u : ℝ := (1/2:ℝ)^(-|e|)
  have hl : 0<l := rpow_pos_of_pos (by norm_num) _
  have hu : 0<u := rpow_pos_of_pos (by norm_num) _
  refine ⟨c₀*c₁*(c₂/C₂*l),C₀*C₁*(C₂/c₂*u),by positivity,by positivity,?_⟩
  filter_upwards [hangle,(tendsto_add_atTop_nat 1).eventually hA,
    (tendsto_add_atTop_nat 1).eventually hB] with n hnangle hnA hnB
  intro k hk
  have hkn : k≤n := by omega
  obtain ⟨hslo,hshi⟩ := hnangle k hk
  obtain ⟨hAlo,hAhi⟩ := hnA.2 k (by omega)
  obtain ⟨hBlo,hBhi⟩ := hnB.2 (n-k) (by omega)
  obtain ⟨hBnlo,hBnhi⟩ := hnB.2 n (by omega)
  let x : ℝ := (k:ℝ)+1
  let y : ℝ := (n:ℝ)+1
  let z : ℝ := (n-k:ℕ)+1
  have hx : 0<x := by dsimp [x]; positivity
  have hy : 0<y := by dsimp [y]; positivity
  have hz : 0<z := by dsimp [z]; positivity
  have hzc : z=(n:ℝ)-k+1 := by dsimp [z]; rw [Nat.cast_sub hkn]
  have hkr : 2*(k:ℝ)≤n := by exact_mod_cast hk
  have hk0 := Nat.cast_nonneg k (α:=ℝ)
  have hpow := comparable_powers hy (show y/2≤z by rw [hzc]; dsimp [y]; linarith)
    (show z≤y by rw [hzc]; dsimp [y]; linarith) e
  have hP : 0<sineProduct (step a b (n+1)/2) (2*gamma b) (n-k) := lt_of_lt_of_le (by positivity) hBlo
  have hQ : 0<sineProduct (step a b (n+1)/2) (2*gamma b) n := lt_of_lt_of_le (by positivity) hBnlo
  have hratio_lo : c₂/C₂*l≤
      sineProduct (step a b (n+1)/2) (2*gamma b) (n-k)/sineProduct (step a b (n+1)/2) (2*gamma b) n := by
    calc
      _ ≤ c₂/C₂*(z^e/y^e) := mul_le_mul_of_nonneg_left
        ((le_div_iff₀ (rpow_pos_of_pos hy e)).mpr hpow.1) (div_pos hc₂ hC₂).le
      _ = (c₂*z^e)/(C₂*y^e) := by ring
      _ ≤ sineProduct (step a b (n+1)/2) (2*gamma b) (n-k)/
        sineProduct (step a b (n+1)/2) (2*gamma b) n := div_le_div₀ hP.le hBlo hQ hBnhi
  have hratio_hi :
      sineProduct (step a b (n+1)/2) (2*gamma b) (n-k)/sineProduct (step a b (n+1)/2) (2*gamma b) n≤C₂/c₂*u := by
    calc
      _ ≤ (C₂*z^e)/(c₂*y^e) := div_le_div₀ (by positivity) hBhi (by positivity) hBnlo
      _ = C₂/c₂*(z^e/y^e) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((div_le_iff₀ (rpow_pos_of_pos hy e)).mpr hpow.2) (div_pos hC₂ hc₂).le
  have hs : 0≤sin (jacobi.Jacobi.modelAngle a b (n+1) k)/sin (jacobi.Jacobi.modelAngle a b (n+1) 0) :=
    (by positivity : 0≤c₀*x).trans hslo
  have hAp : 0<sineProduct (step a b (n+1)/2) (2*gamma a) k := lt_of_lt_of_le (by positivity) hAlo
  have hp : x*x^(2*gamma a-1)=x^(2*gamma a) := by
    calc
      _ = x^(1:ℝ)*x^(2*gamma a-1) := by rw [rpow_one]
      _ = x^(1+(2*gamma a-1)) := (rpow_add hx _ _).symm
      _ = _ := by congr 1; ring
  rw [naturalWeight_ratio ha hb hkn,weightProduct_sineProducts ha hb hkn]
  have hlo := mul_le_mul (mul_le_mul hslo hAlo (by positivity) hs) hratio_lo
    (by positivity) (mul_nonneg hs hAp.le)
  have hhi := mul_le_mul (mul_le_mul hshi hAhi hAp.le (by positivity)) hratio_hi
    (div_pos hP hQ).le (by positivity)
  constructor
  · calc
      _ = (c₀*x)*(c₁*x^(2*gamma a-1))*(c₂/C₂*l) := by rw [← hp]; ring
      _ ≤ (sin (jacobi.Jacobi.modelAngle a b (n+1) k)/sin (jacobi.Jacobi.modelAngle a b (n+1) 0))*
          sineProduct (step a b (n+1)/2) (2*gamma a) k*
            (sineProduct (step a b (n+1)/2) (2*gamma b) (n-k)/sineProduct (step a b (n+1)/2) (2*gamma b) n) := hlo
      _ = _ := by ring
  · calc
      _ = (sin (jacobi.Jacobi.modelAngle a b (n+1) k)/sin (jacobi.Jacobi.modelAngle a b (n+1) 0))*
          sineProduct (step a b (n+1)/2) (2*gamma a) k*
            (sineProduct (step a b (n+1)/2) (2*gamma b) (n-k)/sineProduct (step a b (n+1)/2) (2*gamma b) n) := by ring
      _ ≤ (C₀*x)*(C₁*x^(2*gamma a-1))*(C₂/c₂*u) := hhi
      _ = _ := by rw [← hp]; ring

end
end jacobi.Support
