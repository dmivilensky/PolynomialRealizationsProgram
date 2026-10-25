import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-! Article: Appendix D, Proposition single. Exact root-of-unity phase geometry;
all integer lags are retained, including lags divisible by the period. -/
namespace polyak.General.Regions
noncomputable section

/-- The nearest-root criterion on the entire regular k-gon. -/
theorem polygon_cosine_le {k : ℕ} (hk : 2≤k) {θ : ℝ} (hθ : 0≤θ)
    (hθk : θ≤Real.pi/k) (l : ℕ) (hl : l<k) :
    Real.cos (2*Real.pi*l/k-θ)≤Real.cos θ := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) hk
  have hθpi : θ≤Real.pi := hθk.trans ((div_le_self Real.pi_pos.le (by exact_mod_cast (show 1≤k by omega))).trans le_rfl)
  by_cases hl0 : l=0
  · subst l; simp
  have hl1 : (1:ℝ)≤l := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hl0)
  have hlk : (l:ℝ)≤k-1 := by
    have hh : (l:ℝ)+1≤k := by exact_mod_cast (show l+1≤k by omega)
    linarith
  have hm : 2*Real.pi*l/k=2*(Real.pi*l/k) := by ring
  have hlo : θ≤2*Real.pi*l/k-θ := by
    rw [hm]
    have hp : Real.pi/k≤Real.pi*l/k := div_le_div_of_nonneg_right
      (by nlinarith [Real.pi_pos]) hk0.le
    nlinarith only [hθk,hp]
  have hhi : 2*Real.pi*l/k-θ≤2*Real.pi-θ := by
    rw [hm]
    have hp : Real.pi*l/k≤Real.pi := (div_le_iff₀ hk0).mpr (by nlinarith [Real.pi_pos])
    nlinarith only [hp]
  by_cases hmid : 2*Real.pi*l/k-θ≤Real.pi
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hθ hmid hlo
  · have href : 0≤2*Real.pi-(2*Real.pi*l/k-θ) := by linarith
    have hrefpi : 2*Real.pi-(2*Real.pi*l/k-θ)≤Real.pi := by linarith
    have hreflow : θ≤2*Real.pi-(2*Real.pi*l/k-θ) := by
      have hp : Real.pi*l/k≤Real.pi-Real.pi/k := by
        apply (div_le_iff₀ hk0).mpr
        have hcancel : Real.pi/k*k=Real.pi := div_mul_cancel₀ _ (ne_of_gt hk0)
        nlinarith [mul_le_mul_of_nonneg_left hlk Real.pi_pos.le]
      have hπ : 0≤Real.pi/k := div_nonneg Real.pi_pos.le hk0.le
      linarith
    have hh := Real.cos_le_cos_of_nonneg_of_le_pi hθ hrefpi hreflow
    simpa only [Real.cos_two_pi_sub] using hh

/-- The l=1 comparison already forces the sharp phase bound. -/
theorem phase_le_of_next_cosine {k : ℕ} (hk : 2≤k) {θ : ℝ}
    (_hθ0 : 0≤θ) (hθpi : θ≤Real.pi)
    (h : Real.cos (2*Real.pi/k-θ)≤Real.cos θ) : θ≤Real.pi/k := by
  by_contra hn
  have hθk : Real.pi/k<θ := lt_of_not_ge hn
  have hk0 : (0:ℝ)<k := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0<2) hk
  have hp0 : 0<Real.pi/k := div_pos Real.pi_pos hk0
  have hppi : Real.pi/k<Real.pi := (div_lt_self Real.pi_pos (by exact_mod_cast hk))
  have hs1 : 0<Real.sin (Real.pi/k) := Real.sin_pos_of_pos_of_lt_pi hp0 hppi
  have hs2 : 0<Real.sin (θ-Real.pi/k) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith) (by linarith)
  have hid : Real.cos (2*Real.pi/k-θ)-Real.cos θ=
      2*Real.sin (Real.pi/k)*Real.sin (θ-Real.pi/k) := by
    have he : 2*Real.pi/k-θ=Real.pi/k-(θ-Real.pi/k) := by ring
    have he' : θ=Real.pi/k+(θ-Real.pi/k) := by ring
    have hcs := Real.cos_sub (Real.pi/k) (θ-Real.pi/k)
    have hca := Real.cos_add (Real.pi/k) (θ-Real.pi/k)
    rw [← he] at hcs
    rw [← he'] at hca
    linarith
  nlinarith [mul_pos hs1 hs2]

/-- The sharp finite root-of-unity criterion, including boundary phase locking. -/
theorem polygon_criterion {k : ℕ} (hk : 2≤k) {θ : ℝ}
    (hθ0 : 0≤θ) (hθpi : θ≤Real.pi) :
    (∀ l : ℕ,l<k → Real.cos (2*Real.pi*l/k-θ)≤Real.cos θ) ↔ θ≤Real.pi/k := by
  constructor
  · intro h
    apply phase_le_of_next_cosine hk hθ0 hθpi
    simpa using h 1 (by omega)
  · intro h l hl
    exact polygon_cosine_le hk hθ0 h l hl

/-- Reduce any integer root-of-unity power to one of the k vertices. -/
theorem polygon_cosine_le_int {k : ℕ} (hk : 2≤k) {θ : ℝ} (hθ : 0≤θ)
    (hθk : θ≤Real.pi/k) (m : ℤ) :
    Real.cos (2*Real.pi*m/k-θ)≤Real.cos θ := by
  have hk0 : (0:ℤ)<k := by exact_mod_cast (show 0<k by omega)
  have hkR : (k:ℝ)≠0 := by exact_mod_cast (show k≠0 by omega)
  have he0 : 0≤m%(k:ℤ) := Int.emod_nonneg m (by omega)
  let l := (m%(k:ℤ)).toNat
  have hlc : (l:ℤ)=m%(k:ℤ) := Int.toNat_of_nonneg he0
  have hl : l<k := by
    have he := Int.emod_lt_of_pos m hk0
    exact_mod_cast (show (l:ℤ)<k by rwa [hlc])
  have hdecomp : (m:ℝ)=(l:ℝ)+(k:ℝ)*(m/(k:ℤ):ℤ) := by
    have he := Int.emod_add_ediv_mul m (k:ℤ)
    rw [← hlc] at he
    have hh : (m:ℝ)=(l:ℝ)+(m/(k:ℤ):ℤ)*(k:ℝ) := by exact_mod_cast he.symm
    simpa only [mul_comm] using hh
  have he : 2*Real.pi*m/k-θ=(2*Real.pi*l/k-θ)+(m/(k:ℤ):ℤ)*(2*Real.pi) := by
    rw [hdecomp]
    field_simp
    ring
  rw [he,Real.cos_add_int_mul_two_pi]
  exact polygon_cosine_le hk hθ hθk l hl

/-- Every reduced primitive rotation meets the next root, by Bézout's identity. -/
theorem primitive_next_cosine {j k : ℕ} (hjk : j.Coprime k) (hk : 0<k) (θ : ℝ) :
    Real.cos ((Nat.gcdA j k:ℝ)*(2*Real.pi*j/k)-θ)=Real.cos (2*Real.pi/k-θ) := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast (ne_of_gt hk)
  have hbez : (j:ℝ)*(Nat.gcdA j k:ℝ)+(k:ℝ)*(Nat.gcdB j k:ℝ)=1 := by
    have h := Nat.gcd_eq_gcd_ab j k
    rw [hjk.gcd_eq_one] at h
    exact_mod_cast h.symm
  have he : (Nat.gcdA j k:ℝ)*(2*Real.pi*j/k)-θ=
      (2*Real.pi/k-θ)+(-Nat.gcdB j k:ℤ)*(2*Real.pi) := by
    push_cast
    field_simp
    linear_combination (2*Real.pi)*hbez
  rw [he,Real.cos_add_int_mul_two_pi]

/-- All integer lags of a primitive rational rotation give exactly the sharp phase condition. -/
theorem primitive_phase_criterion {j k : ℕ} (hjk : j.Coprime k) (hk : 2≤k)
    {θ : ℝ} (hθ0 : 0≤θ) (hθpi : θ≤Real.pi) :
    (∀ n : ℤ,Real.cos ((n:ℝ)*(2*Real.pi*j/k)-θ)≤Real.cos θ) ↔ θ≤Real.pi/k := by
  constructor
  · intro h
    apply phase_le_of_next_cosine hk hθ0 hθpi
    simpa only [primitive_next_cosine hjk (show 0<k by omega)] using h (Nat.gcdA j k)
  · intro h n
    have he : (n:ℝ)*(2*Real.pi*j/k)=2*Real.pi*((n*j:ℤ):ℝ)/k := by
      push_cast; ring
    rw [he]
    exact polygon_cosine_le_int hk hθ0 h (n*j)

/-- The two natural lag directions are exactly the integer-lag formulation. -/
theorem integer_phase_iff_two_directions (ω θ : ℝ) :
    (∀ n : ℤ,Real.cos ((n:ℝ)*ω-θ)≤Real.cos θ) ↔
    (∀ n : ℕ,1≤n → Real.cos (n*ω-θ)≤Real.cos θ ∧ Real.cos (n*ω+θ)≤Real.cos θ) := by
  constructor
  · intro h n _
    refine ⟨h n,?_⟩
    have hh := h (-(n:ℤ))
    simp only [Int.cast_neg,Int.cast_natCast,neg_mul] at hh
    rw [show -(n*ω)-θ= -(n*ω+θ) by ring,Real.cos_neg] at hh
    exact hh
  · intro h n
    cases n with
    | ofNat n =>
      by_cases hn : n=0
      · simp [hn]
      · exact (h n (by omega)).1
    | negSucc n =>
      have hh := (h (n+1) (by omega)).2
      simp only [Int.cast_negSucc,neg_mul,Nat.cast_add,Nat.cast_one]
      rw [show -(((n:ℝ)+1)*ω)-θ= -(((n:ℝ)+1)*ω+θ) by ring,Real.cos_neg]
      simpa only [Nat.cast_add,Nat.cast_one] using hh

/-- Proposition single's complete rational-lag cosine criterion. -/
theorem single_harmonic_phase_criterion {j k : ℕ} (hjk : j.Coprime k) (hk : 2≤k)
    {θ : ℝ} (hθ0 : 0≤θ) (hθpi : θ≤Real.pi) :
    (∀ n : ℕ,1≤n → Real.cos (n*(2*Real.pi*j/k)-θ)≤Real.cos θ ∧
      Real.cos (n*(2*Real.pi*j/k)+θ)≤Real.cos θ) ↔ θ≤Real.pi/k := by
  rw [← integer_phase_iff_two_directions]
  exact primitive_phase_criterion hjk hk hθ0 hθpi

end
end polyak.General.Regions
