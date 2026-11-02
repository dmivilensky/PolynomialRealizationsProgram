import jacobi.Analytic.OrderDisk
import jacobi.Analytic.ReferenceStripBounds

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The complete complex-order reference strip bound holds on the very same
closed disk that carries the original numbered Bessel spectrum and its
actual norming products. All parameter margins follow from that disk.
Use: supplies the real application of the complex-order reference estimate in Appendix E.1, with every parameter-set premise discharged.
-/
namespace jacobi.Analytic
noncomputable section
open Set jacobi.ComplexReference
set_option backward.isDefEq.respectTransparency false

/-- The actual reference amplitude has a common full-half-interval minimum bound on every numbered Bessel order disk.
Use: supplies the real application of the complex-order reference
estimate in Appendix E.1, with every parameter-set premise discharged.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the genuine disk lies in Re(alpha)>-1, hence its endpoint exponent
has positive real part and its Gauss denominator exceeds one half.
The affine exponent changes by half the order displacement, so its norm
has one explicit disk bound. Apply the proved complete complex-order
strip theorem with these actual common constants. -/
theorem OrderDisk.reference_strip_bound {a0 : ℝ} (D : OrderDisk a0) (b : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤D.radius →
      ∀ omega : ℂ,omega≠0 → |omega.im|≤b → ∀ t∈Icc (0:ℝ) (1/2),
        ‖jacobi.ComplexReference.wave a omega t‖≤
          C*min (t^(gamma a).re) (‖omega‖^(-(gamma a).re)) := by
  -- The actual spectral disk supplies all uniform bounds; none is an additional GL premise.
  let G : ℝ := ‖gamma (a0:ℂ)‖+D.radius/2+1
  have hG : 0<G := by dsimp [G]; linarith [norm_nonneg (gamma (a0:ℂ)),D.radius_pos]
  obtain ⟨C,hC,hbound⟩ := jacobi.ComplexReference.wave_strip_bound hG (by norm_num : (0:ℝ)<1/2) b
  refine ⟨C,hC,fun a ha omega hne him t ht => ?_⟩
  have har := D.admissible ha
  have hgr : 0<(gamma a).re := by unfold gamma; norm_num; linarith
  have hgc : (1/2:ℝ)≤(gamma a+1/2).re := by unfold gamma; norm_num; linarith
  have hge : gamma a-gamma (a0:ℂ)=(a-(a0:ℂ))/2 := by unfold gamma; ring
  have hgn : ‖gamma a-gamma (a0:ℂ)‖≤D.radius/2 := by
    rw [hge,norm_div]
    norm_num
    exact div_le_div_of_nonneg_right ha (by norm_num)
  have hgG : ‖gamma a‖≤G := by
    have hh := norm_le_norm_sub_add (gamma a) (gamma (a0:ℂ))
    dsimp [G]
    linarith
  exact hbound a omega hgr hgG hgc hne him t ht

end
end jacobi.Analytic
