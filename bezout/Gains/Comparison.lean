import bezout.Gains.Witness
import bezout.Gains.Spectral

/-!
Article: bezout, Theorem 4.1 and the incompatibility paragraph.
Use: every spectral pair is a physical symmetric operator perturbation;
every operator perturbation is an admissible actual-query relative error.
Proof: the explicit two-dimensional witnesses and actual perturbation slopes.
-/

namespace bezout.Gains
noncomputable section
variable {N : ℕ}

/-- The spectral maximum is a lower bound on either universal operator gain. -/
theorem spectralGain_le_operatorGain (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (symmetric : Bool) :
    h.spectralGain I ≤ operatorGain h I symmetric := by
  obtain ⟨x, hx, y, hy, he⟩ := h.spectralGain_attained I
  rw [← he]
  apply le_csInf (operatorBounds_nonempty h I symmetric)
  intro C hb
  exact operatorBound_kernel_norm h I symmetric C hb x y hx hy

/-- The actual-query relative gain bounds operator perturbations from either class. -/
theorem operatorGain_le_localRelativeGain (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (symmetric : Bool) :
    operatorGain h I symmetric ≤ localRelativeGain h I := by
  apply le_csInf (localRelativeBounds_nonempty h I)
  intro C hb
  exact csInf_le ⟨0, fun B hB => operatorBound_nonneg h I symmetric B hB⟩
    (localRelativeBound_operatorBound h I C hb symmetric)

/-- The spectral maximum is a lower bound on the actual-query relative gain. -/
theorem spectralGain_le_localRelativeGain (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) : h.spectralGain I ≤ localRelativeGain h I :=
  (spectralGain_le_operatorGain h I true).trans (operatorGain_le_localRelativeGain h I true)

end
end bezout.Gains
