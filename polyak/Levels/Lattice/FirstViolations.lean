import polyak.Levels.Lattice.Incidence

/-! The first violated modular class is exactly the class of both Farey
parent lags, including the negative upper-parent representative. -/
noncomputable section
namespace polyak.Levels.Lattice

theorem emod_eq_one_iff_incidence {k : ℕ} (hk : 2≤k) (z : ℤ) :
    z%(k:ℤ)=1 ↔ ∃ l : ℤ,z-l*(k:ℤ)=1 := by
  have hkZ : (1:ℤ)<k := by exact_mod_cast hk
  constructor
  · intro h
    refine ⟨z/(k:ℤ),?_⟩
    have he:=Int.emod_add_ediv_mul z (k:ℤ)
    rw [h] at he
    linarith
  · rintro ⟨l,h⟩
    have he : z=1+l*(k:ℤ) := by linarith
    rw [he,Int.add_emod,Int.mul_emod]
    simp only [Int.emod_self,mul_zero,Int.zero_emod,add_zero]
    rw [Int.emod_emod]
    exact Int.emod_eq_of_lt (by norm_num) hkZ

theorem first_violations_zmod_inverse {j k : ℕ} (hjk : j.Coprime k) (hk : 2≤k)
    (n : ℤ) {θ : ℝ} (hθ : Real.pi/k<θ) (hθ₂ : θ≤2*Real.pi/k) (hθπ : θ≤Real.pi) :
    lagValue θ ((n:ℝ)*(2*Real.pi*j/k))<0 ↔ (n : ZMod k)=(j : ZMod k)⁻¹ := by
  rw [first_violations (by omega) j n hθ hθ₂ hθπ,
    emod_eq_one_iff_incidence hk,incidence_iff_zmod_inverse hjk]

theorem first_violations_parent_class {j k : ℕ} (hk : 2≤k)
    (P : FareyParents (j:ℤ) (k:ℤ)) (n : ℤ) {θ : ℝ}
    (hθ : Real.pi/k<θ) (hθ₂ : θ≤2*Real.pi/k) (hθπ : θ≤Real.pi) :
    lagValue θ ((n:ℝ)*(2*Real.pi*j/k))<0 ↔ (k:ℤ)∣n-P.b := by
  rw [first_violations (by omega) j n hθ hθ₂ hθπ,
    emod_eq_one_iff_incidence hk,P.incidence_iff_dvd]

/-- Among all lags below the period, exactly the two signed Farey-parent
lags are the first violations. -/
theorem first_small_violations {j k : ℕ} (hk : 2≤k)
    (P : FareyParents (j:ℤ) (k:ℤ)) (n : ℤ) (hn : |n|<(k:ℤ)) {θ : ℝ}
    (hθ : Real.pi/k<θ) (hθ₂ : θ≤2*Real.pi/k) (hθπ : θ≤Real.pi) :
    lagValue θ ((n:ℝ)*(2*Real.pi*j/k))<0 ↔ n=P.b ∨ n= -P.d := by
  rw [first_violations_parent_class hk P n hθ hθ₂ hθπ,←P.incidence_iff_dvd]
  exact P.small_incidence_iff n hn

end polyak.Levels.Lattice
