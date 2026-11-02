import jacobi.Reference.ContourProduct
import jacobi.Bessel.EdgeData

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
Use: contour_spectral_poles identifies precisely which original sigma and tau zeros lie inside the contours used in the residue theorem.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Metric _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The original midpoint energy contour eventually lies strictly between the two neighboring reference energies with more margin than the full actual spectral displacement.
Use: contour_spectral_poles identifies precisely which original sigma and tau zeros lie inside the contours used in the residue theorem.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the two exact energy margins are pi^2*(m+gamma+1/4) and pi^2*(m+gamma+3/4), and hence eventually exceed the proved uniform displacement constant. -/
theorem contour_spectral_margins {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ (∀ k,|jacobi.Bessel.sigma a ha k-eigenvalue a k|≤C) ∧
      ∃ M : ℕ,∀ m : ℕ,M≤m →
        eigenvalue a m+C< jacobi.Jacobi.endpointCorrection a+(contourRadius a m)^2 ∧
        jacobi.Jacobi.endpointCorrection a+(contourRadius a m)^2<eigenvalue a (m+1)-C := by
  -- The threshold is deduced from the actual global displacement, including its finite small-index part.
  obtain ⟨C,hC,herror⟩ := spectrum_error_bounded ha
  obtain ⟨M,hM⟩ := exists_nat_gt (C+1)
  refine ⟨C,hC,herror,M,fun m hm => ?_⟩
  have hMm : (M:ℝ)≤m := by exact_mod_cast hm
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hm0 := Nat.cast_nonneg (α := ℝ) m
  have hpi : 1≤Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hleft : C<Real.pi^2*((m:ℝ)+gamma a+1/4) :=
    (show C<(m:ℝ)+gamma a+1/4 by linarith).trans_le
      (le_mul_of_one_le_left (by positivity) hpi)
  have hright : C<Real.pi^2*((m:ℝ)+gamma a+3/4) :=
    (show C<(m:ℝ)+gamma a+3/4 by linarith).trans_le
      (le_mul_of_one_le_left (by positivity) hpi)
  have heleft : jacobi.Jacobi.endpointCorrection a+(contourRadius a m)^2-eigenvalue a m=
      Real.pi^2*((m:ℝ)+gamma a+1/4) := by dsimp [contourRadius,eigenvalue]; ring
  have heright : eigenvalue a (m+1)-(jacobi.Jacobi.endpointCorrection a+(contourRadius a m)^2)=
      Real.pi^2*((m:ℝ)+gamma a+3/4) := by dsimp [contourRadius,eigenvalue]; push_cast; ring
  constructor <;> linarith

/-- Each actual spectrum has exactly the original indices zero through m inside every sufficiently large parity circle, with no zero on its boundary.
Use: the finite residue theorem applies to the images of Finset.range(m+1), with all finite pole-set and boundary-exclusion premises discharged for the original spectra.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: use the genuine increasing spectra and the proved neighboring-energy margins. All target energies lie above the original center, so the complex distance to that center is the positive actual energy difference. -/
theorem contour_spectral_poles {a : ℝ} (ha : -1<a) :
    ∃ M : ℕ,∀ m : ℕ,M≤m → ∀ k : ℕ,
      (((jacobi.Bessel.sigma a ha k:ℂ)∈ball (jacobi.Jacobi.endpointCorrection a:ℂ) ((contourRadius a m)^2) ↔ k≤m) ∧
       ((jacobi.Bessel.sigma a ha k:ℂ)∈closedBall (jacobi.Jacobi.endpointCorrection a:ℂ) ((contourRadius a m)^2) ↔ k≤m)) ∧
      (((eigenvalue a k:ℂ)∈ball (jacobi.Jacobi.endpointCorrection a:ℂ) ((contourRadius a m)^2) ↔ k≤m) ∧
       ((eigenvalue a k:ℂ)∈closedBall (jacobi.Jacobi.endpointCorrection a:ℂ) ((contourRadius a m)^2) ↔ k≤m)) := by
  -- Boundary and interior counts are proved together, so no actual pole can remain on the integration circle.
  obtain ⟨C,hC,herror,M,hmargins⟩ := contour_spectral_margins ha
  refine ⟨M,fun m hm k => ?_⟩
  obtain ⟨hl,hr⟩ := hmargins m hm
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hσ : 0< jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a :=
    sub_pos.mpr (jacobi.Bessel.sigma_above_correction ha k)
  have hτ : 0<eigenvalue a k- jacobi.Jacobi.endpointCorrection a := by
    rw [show eigenvalue a k- jacobi.Jacobi.endpointCorrection a=Real.pi^2*((k:ℝ)+gamma a)^2 by dsimp [eigenvalue]; ring]
    positivity
  have hdist (E : ℝ) (hE : 0<E- jacobi.Jacobi.endpointCorrection a) :
      dist (E:ℂ) (jacobi.Jacobi.endpointCorrection a:ℂ)=E- jacobi.Jacobi.endpointCorrection a := by
    rw [dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hE]
  simp only [mem_ball,mem_closedBall,hdist _ hσ,hdist _ hτ]
  by_cases hk : k≤m
  · have hmonoσ := (jacobi.Bessel.sigma_strictMono ha).monotone hk
    have hmonoτ := (eigenvalue_strictMono ha).monotone hk
    have he := le_abs_self (jacobi.Bessel.sigma a ha m-eigenvalue a m) |>.trans (herror m)
    constructor <;> constructor <;> constructor <;> intro <;> first | exact hk | linarith
  · have hkm : m+1≤k := by omega
    have hmonoσ := (jacobi.Bessel.sigma_strictMono ha).monotone hkm
    have hmonoτ := (eigenvalue_strictMono ha).monotone hkm
    have he := neg_le_abs (jacobi.Bessel.sigma a ha (m+1)-eigenvalue a (m+1)) |>.trans (herror (m+1))
    constructor <;> constructor <;> constructor <;> intro h <;> first | exact (hk h).elim | exfalso; linarith

end
end jacobi.Reference
