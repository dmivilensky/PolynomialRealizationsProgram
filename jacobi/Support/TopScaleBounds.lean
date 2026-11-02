import jacobi.Support.SineShiftBounds
import jacobi.Support.Parameters

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The exact first factor s_m in the original top-node product is uniformly
comparable to m+1 throughout the full printed growing half-chain range.
The same shifted-sine bound controls its genuine numerator and denominator.
Use: topValue_bounds combines this with the full original sine-product power estimates to obtain the genuine polynomial growth (m+1)^gamma.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology

/-- The first original top-node sine-product factor has genuine uniform positive linear bounds on the entire printed growing half chain.
Use: topValue_bounds combines this with the full original sine-product power estimates to obtain the genuine polynomial growth (m+1)^gamma.
Article: jacobi, Appendix C.3 (top-node polynomials).
Proof: apply the same proved shifted-sine estimate at original index m+1 in the numerator and at one in the denominator. Their true common positive step cancels, retaining exactly the original m+1 factor. -/
theorem topScale_bounds {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+6→
      c*((m:ℝ)+1)≤sin (((m:ℝ)+averageGamma a b)*step a b n)/sin (averageGamma a b*step a b n) ∧
      sin (((m:ℝ)+averageGamma a b)*step a b n)/sin (averageGamma a b*step a b n)≤C*((m:ℝ)+1) := by
  -- The same genuine shift, including every small index, is used for both numerator and denominator.
  have hg := parameter_pos ha hb
  obtain ⟨c,C,hc,hC,hbound⟩ := shifted_sine_bounds a b
    (show -1<averageGamma a b-1 by linarith [hg.2.2]) 8
  refine ⟨c/C,C/c,div_pos hc hC,div_pos hC hc,?_⟩
  filter_upwards [hbound] with n hn
  intro m hm
  have hh := hn.1
  obtain ⟨hdlo,hdhi⟩ := hn.2 1 (by omega) (by omega)
  obtain ⟨hnlo,hnhi⟩ := hn.2 (m+1) (by omega) (by omega)
  have hdlo' : c*step a b n≤sin (averageGamma a b*step a b n) := by
    convert hdlo using 1 <;> push_cast <;> ring_nf
  have hdhi' : sin (averageGamma a b*step a b n)≤C*step a b n := by
    convert hdhi using 1 <;> push_cast <;> ring_nf
  have hnlo' : c*((m:ℝ)+1)*step a b n≤sin (((m:ℝ)+averageGamma a b)*step a b n) := by
    convert hnlo using 1 <;> push_cast <;> ring_nf
  have hnhi' : sin (((m:ℝ)+averageGamma a b)*step a b n)≤C*((m:ℝ)+1)*step a b n := by
    convert hnhi using 1 <;> push_cast <;> ring_nf
  have hden : 0<sin (averageGamma a b*step a b n) := lt_of_lt_of_le (mul_pos hc hh) hdlo'
  have hm0 : 0<(m:ℝ)+1 := by positivity
  constructor
  · apply (le_div_iff₀ hden).mpr
    have h := mul_le_mul_of_nonneg_left hdhi' (mul_pos (div_pos hc hC) hm0).le
    have he : (c/C*((m:ℝ)+1))*(C*step a b n)=c*((m:ℝ)+1)*step a b n := by field_simp
    rw [he] at h
    exact h.trans hnlo'
  · apply (div_le_iff₀ hden).mpr
    have h := mul_le_mul_of_nonneg_left hdlo' (mul_pos (div_pos hC hc) hm0).le
    have he : (C/c*((m:ℝ)+1))*(c*step a b n)=C*((m:ℝ)+1)*step a b n := by field_simp
    rw [he] at h
    exact hnhi'.trans h

end
end jacobi.Support
