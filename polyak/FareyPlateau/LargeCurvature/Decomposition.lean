import polyak.FareyPlateau.LargeCurvature.SourceData
import polyak.FareyPlateau.LargeCurvature.MiddleZone
import polyak.FareyPlateau.LargeCurvature.CentralZone

noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open General Levels Set
open scoped BigOperators

theorem central_decomposition (n : Fin 3 → ℤ) (w : Fin 3 → ℝ)
    (hsum : ∑ i, w i = 1) {ω₀ c bar δ θ : ℝ}
    (hc : ∀ i, ∃ z : ℤ, (n i:ℝ)*ω₀=2*c+(z:ℝ)*(2*Real.pi)) :
    (∑ i, w i * Geometry.extendedLag (fun _=>θ) (n i) (ω₀+δ)) =
      let ℓ := c+bar*δ/2;
      let g := θ-ℓ;
      let u := fun i => ((n i:ℝ)-bar)/2;
      -2*Real.sin ℓ*Real.sin g+
        (1-∑ i,w i*Real.cos (2*u i*δ))*Real.cos (ℓ-g)+
        Real.sin (ℓ-g)*(∑ i,w i*Real.sin (2*u i*δ)) := by
  dsimp only []
  have hpoint (i : Fin 3) : Geometry.extendedLag (fun _=>θ) (n i) (ω₀+δ) =
      Real.cos θ-Real.cos ((c+bar*δ/2-(θ-(c+bar*δ/2)))+2*(((n i:ℝ)-bar)/2)*δ) := by
    obtain ⟨z,hz⟩ := hc i
    unfold Geometry.extendedLag
    have he : (n i:ℝ)*(ω₀+δ)-θ =
      ((c+bar*δ/2-(θ-(c+bar*δ/2)))+2*(((n i:ℝ)-bar)/2)*δ)+(z:ℝ)*(2*Real.pi) := by
      linear_combination hz
    rw [he,Real.cos_add_int_mul_two_pi]
  have hcos : Real.cos θ - Real.cos (c+bar*δ/2-(θ-(c+bar*δ/2))) =
      -2*Real.sin (c+bar*δ/2)*Real.sin (θ-(c+bar*δ/2)) := by
    rw [Real.cos_sub_cos]
    rw [show (θ+(c+bar*δ/2-(θ-(c+bar*δ/2))))/2=c+bar*δ/2 by ring,
      show (θ-(c+bar*δ/2-(θ-(c+bar*δ/2))))/2=θ-(c+bar*δ/2) by ring]
  have he : ∑ i, w i * (Real.cos θ-Real.cos (c+bar*δ/2-(θ-(c+bar*δ/2)))) =
      Real.cos θ-Real.cos (c+bar*δ/2-(θ-(c+bar*δ/2))) := by
    rw [←Finset.sum_mul,hsum,one_mul]
  simp_rw [hpoint,Real.cos_add]
  rw [←hcos,←he]
  simp only [Fin.sum_univ_succ] at hsum ⊢
  linear_combination Real.cos (c+bar*δ/2-(θ-(c+bar*δ/2)))*hsum

namespace SourceData
variable {q : Tuning} {j k : ℕ} (B : SourceData q j k)

theorem lag_phase (i : Fin 3) : ∃ z : ℤ, (B.n i:ℝ)*B.ω=2*B.c+(z:ℝ)*(2*Real.pi) := by
  have himod : (B.n i*(j:ℤ))%(k:ℤ)=1 := by
    have hh : (B.n i*(j:ℤ))%(k:ℤ)=(B.inverse*(j:ℤ))%(k:ℤ) := by
      rw [Int.mul_emod, B.classes]
      conv_rhs => rw [Int.mul_emod,Int.emod_eq_of_lt B.inverse_pos.le B.inverse_lt]
    rw [hh]
    have hi := B.inverse_mod
    simpa only [Int.ModEq,Int.emod_eq_of_lt (by norm_num : (0:ℤ)≤1)
      (by have := B.period_ge; omega : (1:ℤ)<k)] using hi
  refine ⟨(B.n i*(j:ℤ))/(k:ℤ),?_⟩
  have hh := Int.emod_add_ediv_mul (B.n i*(j:ℤ)) (k:ℤ)
  rw [himod] at hh
  have hr : (1:ℝ)+(((B.n i*(j:ℤ))/(k:ℤ):ℤ):ℝ)*k=(B.n i:ℝ)*j := by exact_mod_cast hh
  change (B.n i:ℝ)*(2*Real.pi*j/k)=2*(Real.pi/k)+_
  calc
    _ = (2*Real.pi/k)*((B.n i:ℝ)*j) := by ring
    _ = (2*Real.pi/k)*(1+(((B.n i*(j:ℤ))/(k:ℤ):ℤ):ℝ)*k) := by rw [←hr]
    _ = _ := by field_simp [B.kp.ne']

end SourceData
end polyak.FareyPlateau.LargeCurvature
