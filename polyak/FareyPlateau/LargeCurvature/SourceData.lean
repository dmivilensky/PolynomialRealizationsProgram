import polyak.FareyPlateau.LargeCurvature.Support
import polyak.FareyPlateau.LargeCurvature.Cutoff
import polyak.FareyPlateau.LargeCurvature.FarProfile

/-! Parameters and the literal three-lag construction of theorem largea.
All fields are source parameters or the source explicit cutoff inequalities. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open General Levels Set
open scoped BigOperators

structure SourceData (q : Tuning) (j k : ℕ) where
  numerator_ge : 2 ≤ j
  period_ge : 5 ≤ k
  numerator_lt : 2*j < k
  inverse : ℤ
  inverse_pos : 0 < inverse
  inverse_lt : inverse < k
  inverse_mod : inverse*(j:ℤ) ≡ 1 [ZMOD (k:ℤ)]
  a : ℝ
  D : ℝ
  M : ℝ
  max_nonneg : 0 ≤ M
  asymmetry_bound : |D| ≤ M
  coefficients : Chart.coefficients q = edgeCoefficients
    (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D
  large : a1 k (Regions.rationalAngle j k) (Chart.rationalHeight j k) M < a

namespace SourceData
variable {q : Tuning} {j k : ℕ} (B : SourceData q j k)

def ω (_B : SourceData q j k) : ℝ := Regions.rationalAngle j k
def c (_B : SourceData q j k) : ℝ := Real.pi/k
def h (_B : SourceData q j k) : ℝ := Chart.rationalHeight j k
def bar : ℝ := Ray.edgeSlope B.ω B.c B.D
def n₀ : ℤ := nearestLag B.inverse k B.bar
def n : Fin 3 → ℤ := integerLag B.n₀ k
def w : Fin 3 → ℝ := weight B.n₀ k B.bar
def N : ℝ := lagBound k B.ω B.M
def ε : ℝ := cosineMargin B.ω (zoneRadius k B.N)

include B

theorem kr : (5:ℝ) ≤ k := by exact_mod_cast B.period_ge
theorem kp : (0:ℝ) < k := by have := B.kr; linarith
theorem ki : (0:ℤ) < k := by have := B.period_ge; omega
theorem ω_mem : B.ω ∈ Ioo (0:ℝ) Real.pi := Regions.rationalAngle_mem (by have := B.numerator_ge; omega) B.numerator_lt

theorem h_nonneg : 0 ≤ B.h := by
  have hs := Real.sin_pos_of_pos_of_lt_pi B.ω_mem.1 B.ω_mem.2
  have hc : 0 ≤ Real.cos (Real.pi/k) := Real.cos_nonneg_of_mem_Icc
    ⟨by have hp : 0 < Real.pi/k := div_pos Real.pi_pos B.kp; linarith [Real.pi_pos],div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by have := B.kr; linarith)⟩
  change 0 ≤ (Real.cos (Real.pi/k) / Real.sin (Real.pi/k))*Real.sin B.ω
  exact mul_nonneg (div_nonneg hc (Real.sin_nonneg_of_nonneg_of_le_pi
    (by positivity) (div_le_self Real.pi_pos.le (by have := B.kr; linarith)))) hs.le

theorem a_pos : 0 < B.a := by
  have hh := (a1_faces B.large).2.2.1
  exact lt_of_le_of_lt (by positivity : 0 ≤ (1+B.M)^2/4) hh

theorem N_ge : 3*(k:ℝ)/2 ≤ B.N := lagBound_ge B.kr B.max_nonneg
theorem N_pos : 0 < B.N := by have := B.N_ge; have := B.kr; linarith

theorem near : |B.bar-(B.n₀:ℝ)| ≤ (k:ℝ)/2 := nearestLag_bound B.ki B.bar

theorem classes (i : Fin 3) : B.n i % (k:ℤ) = B.inverse :=
  integerLag_class ⟨B.inverse_pos.le,B.inverse_lt⟩ (nearestLag_class _ _ _) i

theorem nonzero (i : Fin 3) : B.n i ≠ 0 :=
  integerLag_nonzero ⟨B.inverse_pos,B.inverse_lt⟩ (nearestLag_class _ _ _) i

theorem injective : Function.Injective B.n := integerLag_injective B.ki

theorem coprime : IsCoprime (k:ℤ) B.n₀ := inverse_coprime B.inverse_mod (nearestLag_class _ _ _)

theorem positive (i : Fin 3) : 0 < B.w i := by
  have hh := (weight_bounds B.kp B.near i).1
  exact lt_of_lt_of_le (by norm_num) hh

theorem normalization : ∑ i, B.w i = 1 := weight_sum _ _ _

theorem mean : ∑ i, B.w i * (B.n i : ℝ) = B.bar := by
  simp only [n, integerLag_cast]
  exact weighted_mean B.kp.ne'

theorem lag_abs (i : Fin 3) : |(B.n i : ℝ)| ≤ B.N := by
  have hh := lag_bound B.kp B.near (edgeSlope_bound B.kr B.max_nonneg B.asymmetry_bound) i
  simpa only [n, integerLag_cast, Int.cast_natCast, N, lagBound] using hh

theorem bar_abs : |B.bar| ≤ B.N := by
  have hh := edgeSlope_bound (ω := B.ω) B.kr B.max_nonneg B.asymmetry_bound
  change |B.bar| ≤ slopeBound k B.ω B.M + 3*k/2
  change |B.bar| ≤ _ at hh
  linarith [B.kp]

theorem moment : (k:ℝ)^2/6 ≤ ∑ i, B.w i * (B.n i : ℝ)^2 := by
  simp only [n, integerLag_cast]
  exact second_moment_lower B.kp B.near

theorem admissible : Symbols.Admissible (k:ℤ) B.inverse B.bar B.n B.w := by
  classical
  have hbmod : B.inverse % (k:ℤ) = B.inverse := Int.emod_eq_of_lt B.inverse_pos.le B.inverse_lt
  have hnone (i : Fin 3) : B.n i % (k:ℤ) ≠ 0 := by rw [B.classes]; exact B.inverse_pos.ne'
  refine ⟨B.injective,B.nonzero,B.positive,B.normalization,fun i=>Or.inl (by rw [B.classes,hbmod]),?_,
    integerLag_gcd B.coprime,?_⟩
  · refine ⟨0,1,?_,by rw [B.classes,hbmod],by rw [B.classes,hbmod]⟩
    exact fun h=> (by norm_num : (0:Fin 3)≠1) (B.injective h)
  · have hfilter : Finset.univ.filter (fun i=>B.n i%(k:ℤ)=B.inverse%(k:ℤ))=Finset.univ :=
      Finset.filter_eq_self.mpr (fun i _=>by rw [B.classes,hbmod])
    have hzero : Finset.univ.filter (fun i=>B.n i%(k:ℤ)=0)=∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact hnone i
    rw [hfilter,hzero,Finset.sum_empty]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,B.normalization,B.mean]
    ring

theorem ω_lower : 4*Real.pi/k ≤ B.ω := by
  change 4*Real.pi/k ≤ 2*Real.pi*j/k
  apply div_le_div_of_nonneg_right _ B.kp.le
  have hj : (2:ℝ) ≤ j := by exact_mod_cast B.numerator_ge
  nlinarith [Real.pi_pos]

theorem ω_upper : B.ω ≤ Real.pi-Real.pi/k := by
  change 2*Real.pi*j/k ≤ Real.pi-Real.pi/k
  apply (div_le_iff₀ B.kp).mpr
  have hj : (2:ℝ)*j ≤ k-1 := by
    have hh : (2:ℝ)*j+1 ≤ k := by exact_mod_cast (show 2*j+1 ≤ k by have := B.numerator_lt; omega)
    linarith
  have he : (Real.pi-Real.pi/k)*k=Real.pi*(k-1) := by field_simp [B.kp.ne']
  rw [he]
  nlinarith [Real.pi_pos]

theorem epsilon_lower : 2*sineMargin k/((k:ℝ)*B.N) ≤ B.ε :=
  cosineMargin_lower B.kr B.N_ge B.ω_lower B.ω_upper

theorem epsilon_pos : 0 < B.ε :=
  (div_pos (mul_pos (by norm_num) (sineMargin_pos B.kr)) (mul_pos B.kp B.N_pos)).trans_le B.epsilon_lower

theorem margins : 2*(B.h+2+2*B.M)<B.a*B.ε^2 ∧ 48*B.N^2<B.a*B.ε^2 :=
  cutoff_cosine_margins B.kr B.max_nonneg B.h_nonneg B.large B.epsilon_lower

theorem extra_margins : 6*Real.pi^2*B.N/(k:ℝ)^2 < B.a*B.ε^2 ∧ 24*B.N/(k:ℝ)^2 < B.a*B.ε^2 :=
  cutoff_extra_margins B.kr B.N_ge B.margins.2

end SourceData
end polyak.FareyPlateau.LargeCurvature
