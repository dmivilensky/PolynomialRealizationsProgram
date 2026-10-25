import polyak.FareyPlateau.LargeCurvature.FiniteEstimates

/-! The central-zone quadratic estimate with explicit constants. Curvature
and interval bounds are inputs to this analytic lemma, not feasibility conclusions. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open scoped BigOperators
variable {I : Type*} [Fintype I]

theorem central_symbol_bound (w u : I→ℝ) (hw : ∀i,0≤w i) (hs : ∑i,w i=1)
    (hmean : ∑i,w i*u i=0) {δ ℓ g sh mA δB : ℝ}
    (hsh : 0≤sh) (hℓ : sh≤Real.sin ℓ) (hg : 0≤g ∧ g≤Real.pi/2)
    (hcurve : mA/2*δ^2≤g) (hd : |δ|≤δB) :
    -2*Real.sin ℓ*Real.sin g+
        (1-∑i,w i*Real.cos (2*u i*δ))*Real.cos (ℓ-g)+
        Real.sin (ℓ-g)*(∑i,w i*Real.sin (2*u i*δ)) ≤
      δ^2*(-2*sh*mA/Real.pi+2*(∑i,w i*u i^2)+
        (4/3)*(∑i,w i*|u i|^3)*δB) := by
  have hcos := cosine_error w u hw hs δ
  have hsin := sine_error w u hw hmean δ
  have hgsin : 0≤Real.sin g := Real.sin_nonneg_of_nonneg_of_le_pi hg.1 (by linarith [hg.2,Real.pi_pos])
  have hglower : mA*δ^2/Real.pi≤Real.sin g := by
    have hj := Real.mul_le_sin hg.1 hg.2
    have hc : mA*δ^2/Real.pi≤2/Real.pi*g := by
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right Real.pi_pos).mpr
      nlinarith only [hcurve]
    exact hc.trans hj
  have hnegative : -2*Real.sin ℓ*Real.sin g≤ -2*sh*mA*δ^2/Real.pi := by
    have h₁ := mul_le_mul_of_nonneg_right hℓ hgsin
    have h₂ := mul_le_mul_of_nonneg_left hglower hsh
    calc
      _ ≤ -2*(sh*(mA*δ^2/Real.pi)) := by nlinarith only [h₁,h₂]
      _ = _ := by ring
  have hcosterm : (1-∑i,w i*Real.cos (2*u i*δ))*Real.cos (ℓ-g)≤
      2*(∑i,w i*u i^2)*δ^2 := by
    have hh := mul_le_mul_of_nonneg_left (Real.cos_le_one (ℓ-g)) hcos.1
    have hh' : (1-∑i,w i*Real.cos (2*u i*δ))*Real.cos (ℓ-g)≤1-∑i,w i*Real.cos (2*u i*δ) := by simpa only [mul_one] using hh
    exact hh'.trans hcos.2
  have hU : 0≤∑i,w i*|u i|^3 := Finset.sum_nonneg (fun i _=>by positivity [hw i])
  have hsinterm : Real.sin (ℓ-g)*(∑i,w i*Real.sin (2*u i*δ))≤
      (4/3)*(∑i,w i*|u i|^3)*δB*δ^2 := by
    have hh : Real.sin (ℓ-g)*(∑i,w i*Real.sin (2*u i*δ))≤
        |∑i,w i*Real.sin (2*u i*δ)| := by
      calc
        _ ≤ |Real.sin (ℓ-g)*(∑i,w i*Real.sin (2*u i*δ))| := le_abs_self _
        _ ≤ _ := by rw [abs_mul]; nlinarith [Real.abs_sin_le_one (ℓ-g),abs_nonneg (∑i,w i*Real.sin (2*u i*δ))]
    have hp : |δ|^3≤δB*δ^2 := by
      rw [pow_succ,sq_abs]
      nlinarith only [mul_le_mul_of_nonneg_right hd (sq_nonneg δ)]
    have hmul := mul_le_mul_of_nonneg_left hp (show 0≤(4/3)*(∑i,w i*|u i|^3) by positivity)
    exact hh.trans (hsin.trans (by nlinarith only [hmul]))
  calc
    _ ≤ -2*sh*mA*δ^2/Real.pi+2*(∑i,w i*u i^2)*δ^2+
        (4/3)*(∑i,w i*|u i|^3)*δB*δ^2 :=
      add_le_add (add_le_add hnegative hcosterm) hsinterm
    _ = _ := by ring

end polyak.FareyPlateau.LargeCurvature
