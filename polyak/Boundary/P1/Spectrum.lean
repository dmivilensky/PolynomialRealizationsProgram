import polyak.Boundary.P1.Tail

/-!
Article: Appendix B, the actual one-atom primal spectrum.
Use: finite raw polynomial inequalities and the analytic m≥13 tail imply every
constraint of the original infinite system, then the exact dual proves optimality.
-/
noncomputable section
namespace polyak.Boundary.P1
open Spectral MeasureTheory

def spectrum (a : Frequency) : Spectrum := ⟨Measure.dirac a,by infer_instance⟩

theorem avg_spectrum (a : Frequency) (f : Frequency → ℝ) : avg (spectrum a) f=f a := by
  simp [avg,spectrum]

theorem meanG_spectrum (a : Frequency) (u : ℝ) : meanG (spectrum a) u=1-(a : ℝ)^2-u^2 := by
  rw [meanG_eq_integral,avg_spectrum]
  rfl

def rawSlack (u G d : ℝ) (n : ℕ) (σ a : ℝ) : ℝ :=
  (1-a^2-u^2)*(chebT n G-chebT n a)+
    σ*(2*u*(1-a^2)*chebU (n-1) a)-σ*d*lagDenominator G n

theorem raw_spectrum (a : Frequency) (u t d : ℝ) (ht : t≠0) (n : ℕ)
    (hn : 1≤n) (σ : ℝ) :
    meanA (spectrum a) u t n+σ*meanB (spectrum a) u n-
      σ*(d/Real.sinh t)*Real.sinh (n*t)=rawSlack u (Real.cosh t) d n σ a := by
  have hsh : Real.sinh t≠0 := by simpa using ht
  have hid : d/Real.sinh t*Real.sinh (n*t)=d*lagDenominator (Real.cosh t) n := by
    rw [← lagDenominator_mul_sinh t n hn]
    field_simp [hsh]
  rw [meanA_eq_integral,meanB_eq_integral,avg_spectrum,avg_spectrum]
  unfold rawSlack lagA lagD lagB g
  rw [chebT_cosh]
  rw [show σ*(d/Real.sinh t)*Real.sinh (n*t)=σ*(d/Real.sinh t*Real.sinh (n*t)) by ring,hid]
  ring

theorem exponent_ne_zero {z t : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ht : Real.cosh t=1/z) : t≠0 := by
  rintro rfl
  rw [Real.cosh_zero] at ht
  have he := (eq_div_iff hz.ne').mp ht
  nlinarith

theorem feasibleU_of_raw_prefix {z u t : ℝ} (a : Frequency) (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤(a : ℝ) ∧ (a : ℝ)≤0) (hu : 0≤u) (_hu1 : u≤1)
    (hgz : z/2≤1-(a : ℝ)^2-u^2) (h0 : quartic z u a=0)
    (ht : Real.cosh t=1/z)
    (hprefix : ∀ n : ℕ, 1≤n → n≤12 → ∀ σ : ℝ, σ= -1 ∨ σ=1 →
      0≤rawSlack u (1/z) (chargeNumerator z u a) n σ a) :
    FeasibleU u t (spectrum a) (chargeNumerator z u a/Real.sinh t) := by
  have hgap := minimizer_gap hz hz1 ha hu hgz h0 ht
  have ht0 := exponent_ne_zero hz hz1 ht
  have hstar : |chargeNumerator z u a/Real.sinh t|≤meanG (spectrum a) u := by
    rw [meanG_spectrum]
    have hz3 : 0≤z^3/4 := by positivity
    linarith
  apply feasibleU_of_prefix_tail (spectrum a) u _ t 12 hstar
  · intro n hn hN
    have hl := raw_spectrum a u t (chargeNumerator z u a) ht0 n hn (-1)
    have hU := raw_spectrum a u t (chargeNumerator z u a) ht0 n hn 1
    rw [ht] at hl hU
    have hlow := hprefix n hn hN (-1) (Or.inl rfl)
    have hupp := hprefix n hn hN 1 (Or.inr rfl)
    constructor <;> nlinarith
  · intro n hn
    have hb : meanG (spectrum a) u+2*u^2≤4 := by
      rw [meanG_spectrum]
      nlinarith [sq_nonneg (a : ℝ)]
    have he := tail_at_thirteen hz hz1 ht (by simpa [meanG_spectrum] using hgap) hb n (by omega)
    simpa only [meanG_spectrum] using he.le

theorem optimal_of_raw_prefix {z u t : ℝ} (a : Frequency) (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤(a : ℝ) ∧ (a : ℝ)≤0) (hu : 0≤u) (hu1 : u≤1)
    (hgz : z/2≤1-(a : ℝ)^2-u^2) (h0 : quartic z u a=0)
    (h1 : quarticDerivative z u a=0)
    (hq : |residualLinear z u a|<residualConstant z u a)
    (ht : Real.cosh t=1/z)
    (hprefix : ∀ n : ℕ, 1≤n → n≤12 → ∀ σ : ℝ, σ= -1 ∨ σ=1 →
      0≤rawSlack u (1/z) (chargeNumerator z u a) n σ a) :
    V t=Real.arsinh u := by
  apply primal_dual_optimal weights hu
    (feasibleU_of_raw_prefix a hz hz1 ha hu hu1 hgz h0 ht hprefix)
  intro c
  rw [ht]
  apply dualPolynomial_nonneg hz (by nlinarith : 0<4-z^2)
    (by rw [lt_div_iff₀ hz]; nlinarith : 1<1/z) h0 h1 hq c

end polyak.Boundary.P1
