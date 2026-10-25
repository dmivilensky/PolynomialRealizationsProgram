import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-! The explicit positive three-lag symbol of theorem largea. The middle
lag can coincide with the slope index; no nonresonance hypothesis is used. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open scoped BigOperators

def nearestLag (b k : ℤ) (s : ℝ) : ℤ := b+k*round ((s-b)/k)

theorem nearestLag_bound {b k : ℤ} (hk : 0<k) (s : ℝ) :
    |s-(nearestLag b k s : ℝ)| ≤ (k:ℝ)/2 := by
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  have hr := abs_sub_round ((s-b)/k)
  have hp : |(k:ℝ)*((s-b)/k-(round ((s-b)/k):ℝ))| ≤ (k:ℝ)/2 := by
    rw [abs_mul,abs_of_pos hkr]
    nlinarith only [mul_le_mul_of_nonneg_left hr hkr.le]
  have he : (k:ℝ)*((s-b)/k-(round ((s-b)/k):ℝ))=s-(nearestLag b k s:ℝ) := by
    dsimp [nearestLag]
    push_cast
    field_simp
    ring
  rw [he] at hp
  nlinarith only [hp]

theorem nearestLag_class (b k : ℤ) (s : ℝ) : k∣nearestLag b k s-b := by
  refine ⟨round ((s-b)/k),?_⟩
  dsimp [nearestLag]
  ring

def tilt (n k s : ℝ) : ℝ := (s-n)/(2*k)
def lag (n k : ℝ) : Fin 3 → ℝ := ![n-k,n,n+k]
def weight (n k s : ℝ) : Fin 3 → ℝ := ![1/3-tilt n k s,1/3,1/3+tilt n k s]
def deviation (n k s : ℝ) (i : Fin 3) : ℝ := (lag n k i-s)/2

theorem tilt_bounds {n k s : ℝ} (hk : 0<k) (hnear : |s-n|≤k/2) :
    -(1/4)≤tilt n k s ∧ tilt n k s≤1/4 := by
  obtain ⟨hl,hu⟩ := abs_le.mp hnear
  unfold tilt
  constructor
  · apply (le_div_iff₀ (by positivity : 0<2*k)).mpr
    linarith
  · apply (div_le_iff₀ (by positivity : 0<2*k)).mpr
    linarith

theorem weight_bounds {n k s : ℝ} (hk : 0<k) (hnear : |s-n|≤k/2) (i : Fin 3) :
    (1/12:ℝ)≤weight n k s i ∧ weight n k s i≤7/12 := by
  have ht := tilt_bounds hk hnear
  fin_cases i <;> norm_num [weight] <;> constructor <;> linarith

theorem weight_sum (n k s : ℝ) : ∑ i,weight n k s i=1 := by
  simp [weight,Fin.sum_univ_succ]
  ring

theorem weighted_mean {n k s : ℝ} (hk : k≠0) :
    ∑ i,weight n k s i*lag n k i=s := by
  simp [weight,lag,Fin.sum_univ_succ,tilt]
  field_simp
  ring

theorem deviation_mean {n k s : ℝ} (hk : k≠0) :
    ∑ i,weight n k s i*deviation n k s i=0 := by
  simp [weight,lag,deviation,Fin.sum_univ_succ,tilt]
  field_simp
  ring

theorem deviation_bound {n k s : ℝ} (hk : 0<k) (hnear : |s-n|≤k/2) (i : Fin 3) :
    |deviation n k s i|≤3*k/4 := by
  obtain ⟨hl,hu⟩ := abs_le.mp hnear
  rw [abs_le]
  fin_cases i <;> norm_num [deviation,lag] <;> constructor <;> linarith

theorem second_moment {n k s : ℝ} (hk : k≠0) :
    ∑ i,weight n k s i*lag n k i^2 = s^2+4*(∑ i,weight n k s i*deviation n k s i^2) := by
  simp [weight,lag,deviation,Fin.sum_univ_succ,tilt]
  field_simp
  ring

theorem variance_lower {n k s : ℝ} (hk : 0<k) (hnear : |s-n|≤k/2) :
    k^2/24≤∑ i,weight n k s i*deviation n k s i^2 := by
  have h₀ := (weight_bounds hk hnear 0).1
  have h₁ := (weight_bounds hk hnear 1).1
  have h₂ := (weight_bounds hk hnear 2).1
  have h₀p := mul_nonneg (by linarith : 0≤weight n k s 0-1/12) (sq_nonneg (deviation n k s 0))
  have h₁p := mul_nonneg (by linarith : 0≤weight n k s 1) (sq_nonneg (deviation n k s 1))
  have h₂p := mul_nonneg (by linarith : 0≤weight n k s 2-1/12) (sq_nonneg (deviation n k s 2))
  simp only [Fin.sum_univ_succ]
  norm_num [deviation,lag] at *
  nlinarith [sq_nonneg (n-s)]

theorem second_moment_lower {n k s : ℝ} (hk : 0<k) (hnear : |s-n|≤k/2) :
    k^2/6≤∑ i,weight n k s i*lag n k i^2 := by
  rw [second_moment hk.ne']
  nlinarith [variance_lower hk hnear,sq_nonneg s]

theorem variance_upper {n k s : ℝ} (hk : 0<k) (hnear : |s-n|≤k/2) :
    (∑ i,weight n k s i*deviation n k s i^2) ≤ 9/16*k^2 := by
  have hp (i : Fin 3) : weight n k s i*deviation n k s i^2≤weight n k s i*(9/16*k^2) := by
    apply mul_le_mul_of_nonneg_left _ (by have hh := (weight_bounds hk hnear i).1; linarith)
    have hd := deviation_bound hk hnear i
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0≤3*k/4)).mpr hd
    rw [sq_abs] at hs
    nlinarith only [hs]
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=> hp i)
  rw [← Finset.sum_mul,weight_sum,one_mul] at hh
  exact hh

theorem third_moment_upper {n k s : ℝ} (hk : 0<k) (hnear : |s-n|≤k/2) :
    (∑ i,weight n k s i*|deviation n k s i|^3) ≤ 27/64*k^3 := by
  have hp (i : Fin 3) : weight n k s i*|deviation n k s i|^3≤weight n k s i*(27/64*k^3) := by
    apply mul_le_mul_of_nonneg_left _ (by have hh := (weight_bounds hk hnear i).1; linarith)
    have hd := pow_le_pow_left₀ (abs_nonneg _) (deviation_bound hk hnear i) 3
    nlinarith only [hd]
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ)=> hp i)
  rw [← Finset.sum_mul,weight_sum,one_mul] at hh
  exact hh

theorem lag_bound {n k s N : ℝ} (hk : 0<k) (hnear : |s-n|≤k/2)
    (hN : |s|≤N) (i : Fin 3) : |lag n k i|≤N+3*k/2 := by
  obtain ⟨hl,hu⟩ := abs_le.mp hnear
  obtain ⟨hs₀,hs₁⟩ := abs_le.mp hN
  rw [abs_le]
  fin_cases i <;> norm_num [lag] <;> constructor <;> linarith

end polyak.FareyPlateau.LargeCurvature
