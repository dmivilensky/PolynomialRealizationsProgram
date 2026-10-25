import polyak.FareyPlateau.LargeCurvature.FarDenominator
import polyak.FareyPlateau.LargeCurvature.Constants
import polyak.FareyPlateau.Symbols.Admissible

noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open scoped BigOperators

theorem integerLag_injective {n k : ℤ} (hk : 0 < k) : Function.Injective (integerLag n k) := by
  intro i l hil
  fin_cases i <;> fin_cases l <;> simp_all [integerLag] <;> omega

theorem integerLag_class {n k b : ℤ} (hb : 0 ≤ b ∧ b < k) (hn : k ∣ n-b) (i : Fin 3) :
    integerLag n k i % k = b := by
  have hnb : n % k = b := by
    have hh := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp hn)
    exact hh.trans (Int.emod_eq_of_lt hb.1 hb.2)
  fin_cases i <;> simp [integerLag, hnb]

theorem integerLag_nonzero {n k b : ℤ} (hb : 0 < b ∧ b < k) (hn : k ∣ n-b) (i : Fin 3) :
    integerLag n k i ≠ 0 := by
  intro hz
  have hh := integerLag_class ⟨hb.1.le,hb.2⟩ hn i
  rw [hz,Int.zero_emod] at hh
  omega

theorem inverse_coprime {j k b n : ℤ} (hb : b*j ≡ 1 [ZMOD k]) (hn : k ∣ n-b) :
    IsCoprime k n := by
  obtain ⟨z,hz⟩ := (Int.modEq_iff_dvd).mp hb
  obtain ⟨r,hr⟩ := hn
  refine ⟨z-r*j,j,?_⟩
  linear_combination -hz+j*hr

theorem integerLag_gcd {n k : ℤ} (hn : IsCoprime k n) : Finset.univ.gcd (integerLag n k) = 1 := by
  let g := Finset.univ.gcd (integerLag n k)
  have h₁ : g ∣ n := by simpa [g, integerLag] using (Finset.gcd_dvd (f := integerLag n k) (Finset.mem_univ (1 : Fin 3)))
  have h₂ : g ∣ n+k := by simpa [g, integerLag] using (Finset.gcd_dvd (f := integerLag n k) (Finset.mem_univ (2 : Fin 3)))
  have hk : g ∣ k := by simpa using dvd_sub h₂ h₁
  obtain ⟨a,b,hab⟩ := hn
  have hg : g ∣ 1 := by rw [← hab]; exact dvd_add (dvd_mul_of_dvd_right hk a) (dvd_mul_of_dvd_right h₁ b)
  rw [← Finset.normalize_gcd, normalize_eq_one]
  exact isUnit_of_dvd_one hg

end polyak.FareyPlateau.LargeCurvature
