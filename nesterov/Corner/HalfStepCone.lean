import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! The elementary half-step cone kernels and their rational atoms. -/
namespace nesterov.Corner
noncomputable section

def halfStepUpper (ω : ℝ) (n : ℕ) : ℝ :=
  Real.sin ((n:ℝ)*ω/2)*Real.sin (((n:ℝ)+1)*ω/2)

def halfStepLower (ω : ℝ) (n : ℕ) : ℝ :=
  Real.sin ((n:ℝ)*ω/2)*Real.sin (((n:ℝ)-1)*ω/2)

theorem halfStepLower_succ (ω : ℝ) (n : ℕ) :
    halfStepLower ω (n+1)=halfStepUpper ω n := by
  simp only [halfStepLower,halfStepUpper,Nat.cast_add,Nat.cast_one]
  have he : ((n:ℝ)+1)-1=(n:ℝ) := by ring
  rw [he,mul_comm]

theorem halfStepUpper_period {K : ℕ} (hK : 0<K) (n : ℕ) :
    halfStepUpper (2*Real.pi/K) (n+K)=halfStepUpper (2*Real.pi/K) n := by
  have hk : (K:ℝ)≠0 := by positivity
  have he (x : ℝ) : (x+(K:ℝ))*(2*Real.pi/K)/2=x*(2*Real.pi/K)/2+Real.pi := by
    field_simp
  unfold halfStepUpper
  rw [Nat.cast_add,he]
  have he' : ((n:ℝ)+(K:ℝ)+1)*(2*Real.pi/K)/2=
      ((n:ℝ)+1)*(2*Real.pi/K)/2+Real.pi := by
    (convert he ((n:ℝ)+1) using 1; ring)
  rw [he',Real.sin_add_pi,Real.sin_add_pi]
  ring

theorem halfStepUpper_atom {K : ℕ} (hK : 2≤K) (n : ℕ) :
    0≤halfStepUpper (2*Real.pi/K) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<K
    · have hk : (0:ℝ)<K := by positivity
      have hn' : (n:ℝ)+1≤K := by exact_mod_cast (show n+1≤K by omega)
      have hω : 0≤2*Real.pi/(K:ℝ) := by positivity
      have hbound : ((n:ℝ)+1)*(2*Real.pi/K)/2≤Real.pi := by
        apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
        rw [←mul_div_assoc]
        apply (div_le_iff₀ hk).mpr
        nlinarith [mul_le_mul_of_nonneg_right hn' Real.pi_pos.le]
      apply mul_nonneg
      · apply Real.sin_nonneg_of_nonneg_of_le_pi
        · positivity
        · have hh : (n:ℝ)*(2*Real.pi/K)/2≤((n:ℝ)+1)*(2*Real.pi/K)/2 := by
            nlinarith
          exact hh.trans hbound
      · exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hbound
    · have hnK : K≤n := by omega
      have hlt : n-K<n := by omega
      have he : n-K+K=n := Nat.sub_add_cancel hnK
      rw [←he,halfStepUpper_period (by omega : 0<K)]
      exact ih (n-K) hlt

theorem halfStepLower_atom {K : ℕ} (hK : 2≤K) (n : ℕ) :
    0≤halfStepLower (2*Real.pi/K) n := by
  cases n with
  | zero => simp [halfStepLower]
  | succ n => rw [halfStepLower_succ]; exact halfStepUpper_atom hK n

theorem halfStepUpper_gap_negative {K : ℕ} (hK : 2≤K) {ω : ℝ}
    (hlo : 2*Real.pi/((K:ℝ)+1)<ω) (hhi : ω<2*Real.pi/K) :
    halfStepUpper ω K<0 := by
  have hk : (0:ℝ)<K := by positivity
  have hk2 : (2:ℝ)≤K := by exact_mod_cast hK
  have hω : 0<ω := lt_trans (by positivity) hlo
  have hlow : 2*Real.pi<ω*((K:ℝ)+1) := (div_lt_iff₀ (by positivity)).mp hlo
  have hhigh : ω*(K:ℝ)<2*Real.pi := (lt_div_iff₀ hk).mp hhi
  have hωπ : ω<Real.pi := by nlinarith [mul_le_mul_of_nonneg_left hk2 hω.le]
  have hs : 0<Real.sin ((K:ℝ)*ω/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have ht : 0<Real.sin ((((K:ℝ)+1)*ω/2)-Real.pi) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  have he : Real.sin (((K:ℝ)+1)*ω/2)=
      -Real.sin ((((K:ℝ)+1)*ω/2)-Real.pi) := by
    calc
      _=Real.sin (((((K:ℝ)+1)*ω/2)-Real.pi)+Real.pi) := congrArg Real.sin (by ring)
      _=_ := Real.sin_add_pi _
  unfold halfStepUpper
  rw [he]
  exact mul_neg_of_pos_of_neg hs (neg_neg_of_pos ht)

theorem halfStep_cos_gap (ω : ℝ) (K : ℕ) :
    Real.cos (ω/2)-Real.cos (((K:ℝ)+1/2)*ω)=2*halfStepUpper ω K := by
  rw [Real.cos_sub_cos]
  have h1 : (ω/2+((K:ℝ)+1/2)*ω)/2=((K:ℝ)+1)*ω/2 := by ring
  have h2 : (ω/2-((K:ℝ)+1/2)*ω)/2=-((K:ℝ)*ω/2) := by ring
  rw [h1,h2,Real.sin_neg]
  unfold halfStepUpper
  ring

theorem halfStepLower_gap_negative {K : ℕ} (hK : 2≤K) {ω : ℝ}
    (hlo : 2*Real.pi/((K:ℝ)+1)<ω) (hhi : ω<2*Real.pi/K) :
    halfStepLower ω (K+1)<0 := by
  rw [halfStepLower_succ]
  exact halfStepUpper_gap_negative hK hlo hhi

theorem halfStep_cos_gap_negative {K : ℕ} (hK : 2≤K) {ω : ℝ}
    (hlo : 2*Real.pi/((K:ℝ)+1)<ω) (hhi : ω<2*Real.pi/K) :
    Real.cos (ω/2)-Real.cos (((K:ℝ)+1/2)*ω)<0 := by
  rw [halfStep_cos_gap]
  exact mul_neg_of_pos_of_neg (by norm_num) (halfStepUpper_gap_negative hK hlo hhi)

end
end nesterov.Corner
