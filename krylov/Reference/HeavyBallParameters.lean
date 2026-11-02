import chebyshev1.Chebyshev.Normalization
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(b), genuine printed heavy-ball parameters.
Use: identify the actual pivot, coupling, spectral endpoints and Chebyshev coordinate with the original square-root formulas in mu and L.
Source: elementary real square-root identities on the actual strictly positive spectral interval.
-/

namespace krylov.Reference
noncomputable section
open chebyshev1
namespace HeavyBallParameters

/-- The genuine printed heavy-ball reciprocal-line pivot from the original spectral endpoints.
Use: The genuine printed heavy-ball reciprocal-line pivot from the original spectral endpoints.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball parameters.
Proof: Use the actual squared sum of positive spectral roots. -/
def pivot (I : SpectralInterval) : ℝ := (Real.sqrt I.L+Real.sqrt I.mu)^2/4

/-- The genuine printed optimal heavy-ball ratio from the original spectral endpoints.
Use: The genuine printed optimal heavy-ball ratio from the original spectral endpoints.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball parameters.
Proof: Use the actual difference-to-sum ratio of their positive square roots. -/
def ratio (I : SpectralInterval) : ℝ :=
  (Real.sqrt I.L-Real.sqrt I.mu)/(Real.sqrt I.L+Real.sqrt I.mu)

/-- The genuine spectral square roots have the actual strict signs and separation needed by all printed parameters.
Use: The genuine spectral square roots have the actual strict signs and separation needed by all printed parameters.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball parameters.
Proof: Use monotonicity and positivity of the actual real square root. -/
theorem roots_domain (I : SpectralInterval) :
    0 < Real.sqrt I.mu ∧ Real.sqrt I.mu<Real.sqrt I.L ∧ 0 < Real.sqrt I.L+Real.sqrt I.mu := by
  have hm := Real.sqrt_pos.mpr I.mu_pos
  have hl := Real.sqrt_lt_sqrt I.mu_pos.le I.mu_lt_L
  exact ⟨hm,hl,by linarith⟩

/-- The genuine printed heavy-ball pivot is positive.
Use: The genuine printed heavy-ball pivot is positive.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball parameters.
Proof: The actual spectral-root sum is strictly positive. -/
theorem pivot_pos (I : SpectralInterval) : 0 < pivot I := by
  unfold pivot
  exact div_pos (sq_pos_of_pos (roots_domain I).2.2) (by norm_num)

/-- The genuine printed heavy-ball ratio lies strictly between zero and one.
Use: The genuine printed heavy-ball ratio lies strictly between zero and one.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball parameters.
Proof: Compare the actual positive spectral-root difference and sum. -/
theorem ratio_domain (I : SpectralInterval) : 0 < ratio I ∧ ratio I<1 := by
  unfold ratio
  exact ⟨div_pos (sub_pos.mpr (roots_domain I).2.1) (roots_domain I).2.2,
    (div_lt_one (roots_domain I).2.2).mpr (by linarith [(roots_domain I).1])⟩

/-- The actual lower squared heavy-ball endpoint equals the original mu.
Use: The actual lower squared heavy-ball endpoint equals the original mu.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball parameters.
Proof: Cancel the true nonzero spectral-root sum and square the genuine lower root. -/
theorem lower_endpoint (I : SpectralInterval) : pivot I*(1-ratio I)^2=I.mu := by
  -- The genuine affine lower endpoint factor cancels against the actual positive square-root sum.
  have hden := (roots_domain I).2.2.ne'
  have he : 1-ratio I=2*Real.sqrt I.mu/(Real.sqrt I.L+Real.sqrt I.mu) := by
    unfold ratio
    field_simp
    ring
  rw [he]
  calc
    _ = (Real.sqrt I.mu)^2 := by unfold pivot;field_simp;ring
    _ = I.mu := Real.sq_sqrt I.mu_pos.le

/-- The actual upper squared heavy-ball endpoint equals the original L.
Use: The actual upper squared heavy-ball endpoint equals the original L.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball parameters.
Proof: Cancel the true nonzero spectral-root sum and square the genuine upper root. -/
theorem upper_endpoint (I : SpectralInterval) : pivot I*(1+ratio I)^2=I.L := by
  -- The genuine affine upper endpoint factor cancels against the actual positive square-root sum.
  have hden := (roots_domain I).2.2.ne'
  have he : 1+ratio I=2*Real.sqrt I.L/(Real.sqrt I.L+Real.sqrt I.mu) := by
    unfold ratio
    field_simp
    ring
  rw [he]
  calc
    _ = (Real.sqrt I.L)^2 := by unfold pivot;field_simp;ring
    _ = I.L := Real.sq_sqrt (I.mu_pos.trans I.mu_lt_L).le

/-- The actual pivot times ratio equals the original printed adjacent coupling.
Use: The actual pivot times ratio equals the original printed adjacent coupling.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball parameters.
Proof: Use the true difference of squared spectral roots. -/
theorem edge (I : SpectralInterval) : pivot I*ratio I=(I.L-I.mu)/4 := by
  -- The actual adjacent coupling is the difference of the genuine squared spectral roots.
  have hden := (roots_domain I).2.2.ne'
  calc
    _ = ((Real.sqrt I.L)^2-(Real.sqrt I.mu)^2)/4 := by unfold pivot ratio;field_simp;ring
    _ = _ := by rw [Real.sq_sqrt (I.mu_pos.trans I.mu_lt_L).le,Real.sq_sqrt I.mu_pos.le]

/-- The actual internal heavy-ball diagonal equals the original spectral midpoint.
Use: The actual internal heavy-ball diagonal equals the original spectral midpoint.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball parameters.
Proof: Use the true sum of squared spectral roots. -/
theorem diagonal (I : SpectralInterval) : pivot I*(1+ratio I^2)=(I.L+I.mu)/2 := by
  -- The actual internal diagonal is the sum of the genuine squared spectral roots.
  have hden := (roots_domain I).2.2.ne'
  calc
    _ = ((Real.sqrt I.L)^2+(Real.sqrt I.mu)^2)/2 := by unfold pivot ratio;field_simp;ring
    _ = _ := by rw [Real.sq_sqrt (I.mu_pos.trans I.mu_lt_L).le,Real.sq_sqrt I.mu_pos.le]

/-- The true heavy-ball recurrence coordinate equals the original affine spectral coordinate.
Use: The true heavy-ball recurrence coordinate equals the original affine spectral coordinate.
Article: main_krylov, prop:phi(b), genuine printed heavy-ball parameters.
Proof: Insert the genuine pivot, midpoint and edge identities and cancel only their actual positive domains. -/
theorem coordinate (I : SpectralInterval) (lam : ℝ) :
    (1+ratio I^2-(pivot I)⁻¹*lam)/(2*ratio I)=I.z lam := by
  -- Use the actual pivot and edge identities before identifying the true physical affine coordinate.
  have hd := (pivot_pos I).ne'
  have hq := (ratio_domain I).1.ne'
  calc
    _ = (pivot I*(1+ratio I^2)-lam)/(2*(pivot I*ratio I)) := by field_simp
    _ = I.z lam := by rw [diagonal,edge];unfold SpectralInterval.z SpectralInterval.delta;field_simp;ring
end HeavyBallParameters
end
end krylov.Reference
