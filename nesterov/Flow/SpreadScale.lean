import nesterov.Flow.SpreadBounds

/-! Article: Lemma `lem:spread`, choose the frequency scale before the grid. -/
namespace nesterov.Flow
noncomputable section
open Finset

theorem exists_spread_scale {θ m c Q u d : ℝ}
    (hc : 0<c) (hQ : 1≤Q) (hu : 0<u) (hd : 0<d)
    (hdelta : 0<delta θ m c) (ha : 0<(3*c-θ)/c) :
    ∃ γ₀ : ℝ,1≤γ₀ ∧ 2*c≤γ₀ ∧ c*Q≤γ₀ ∧
      16*delta θ m c≤γ₀^2 ∧ delta θ m c+1≤γ₀^2 ∧
      (c*delta θ m c+1)≤(3*c-θ)*γ₀^2 ∧
      (4*c*Q+2*c)*γ₀+3*delta θ m c≤γ₀^2*u/4 ∧
      (2*delta θ m c+2*c*γ₀)/d+delta θ m c/((3*c-θ)/c)≤γ₀^2/4 := by
  classical
  let A : ℝ := 4*c*Q+2*c
  let B : ℝ := 3*delta θ m c
  let P : ℝ := 2*c/d
  let R : ℝ := 2*delta θ m c/d+delta θ m c/((3*c-θ)/c)
  have hA : 0≤A := by dsimp [A]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have hP : 0≤P := by dsimp [P]; positivity
  have hR : 0≤R := by dsimp [R]; positivity
  have hnum : 0<3*c-θ := (div_pos_iff_of_pos_right hc).mp ha
  let s : Finset ℝ := {1,2*c,c*Q,16*delta θ m c,delta θ m c+1,
    (c*delta θ m c+1)/(3*c-θ),4*(A+B)/u,4*(P+R)}
  have hs : s.Nonempty := by simp [s]
  let γ₀ := s.max' hs
  have hγ (x : ℝ) (hx : x∈s) : x≤γ₀ := le_max' s x hx
  have h1 : 1≤γ₀ := hγ _ (by simp [s])
  have h2 : 2*c≤γ₀ := hγ _ (by simp [s])
  have h3 : c*Q≤γ₀ := hγ _ (by simp [s])
  have h4 : 16*delta θ m c≤γ₀ := hγ _ (by simp [s])
  have h5 : delta θ m c+1≤γ₀ := hγ _ (by simp [s])
  have h6 : (c*delta θ m c+1)/(3*c-θ)≤γ₀ := hγ _ (by simp [s])
  have h7 : 4*(A+B)/u≤γ₀ := hγ _ (by simp [s])
  have h8 : 4*(P+R)≤γ₀ := hγ _ (by simp [s])
  have hsq : γ₀≤γ₀^2 := by nlinarith
  refine ⟨γ₀,h1,h2,h3,h4.trans hsq,h5.trans hsq,?_,?_,?_⟩
  · have hh := (div_le_iff₀ hnum).mp h6
    have hi := mul_le_mul_of_nonneg_left hsq hnum.le
    nlinarith
  · have hh := (div_le_iff₀ hu).mp h7
    have hi := mul_le_mul_of_nonneg_right hh (show 0≤γ₀ by linarith)
    have hj := mul_le_mul_of_nonneg_left h1 hB
    dsimp only [A,B] at *
    nlinarith only [hi,hj]
  · have hh := mul_le_mul_of_nonneg_right h8 (show 0≤γ₀ by linarith)
    have hi := mul_le_mul_of_nonneg_left h1 hR
    have he : (2*delta θ m c+2*c*γ₀)/d+delta θ m c/((3*c-θ)/c)=P*γ₀+R := by
      dsimp [P,R]
      ring
    rw [he]
    nlinarith only [hh,hi]

end
end nesterov.Flow
