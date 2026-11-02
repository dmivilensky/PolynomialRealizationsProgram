import jacobi.Support.SinePowerBounds

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The full original support ranges are proved, both at h=pi/N and at
h/2, with the same actual positive constants. All sufficiently-large
degree and compact sine-argument conditions are discharged from the
literal original affine frequency.
Use: top-node growth, difference estimates and spectral-weight envelopes use these same genuine finite sine products throughout the original growing degree ranges.
-/
namespace jacobi.Support
noncomputable section
open Real Filter
open scoped Topology

/-- The original support sine products have the complete printed uniform power bounds, including the original half-step extension.
Use: top-node growth, difference estimates and spectral-weight envelopes use these same genuine finite sine products throughout the original growing degree ranges.
Article: jacobi, Appendix C.3 (sine-product estimates).
Proof: choose the fixed compact sine-coordinate interval [0,3/4] in the proved arbitrary-frequency product bounds. The original frequency is n plus a fixed real offset; for every sufficiently large actual degree, both stated growing ranges lie in that compact interval. The same two constants therefore apply to both original steps. -/
theorem support_sineProduct_bounds (a b : ℝ) {s : ℝ} (hs:0<s) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,
      (∀m:ℕ,2*m≤n+6→
        c*((m:ℝ)+1)^(s-1)≤sineProduct (step a b n) s m ∧
        sineProduct (step a b n) s m≤C*((m:ℝ)+1)^(s-1)) ∧
      (∀m:ℕ,m≤n+3→
        c*((m:ℝ)+1)^(s-1)≤sineProduct (step a b n/2) s m ∧
        sineProduct (step a b n/2) s m≤C*((m:ℝ)+1)^(s-1)) := by
  -- The finite thresholds depend only on the original fixed parameters and the shift, never on the growing mesh index.
  obtain ⟨c,C,hc,hC,hbound⟩ := sineProduct_power_bounds hs (by norm_num : (0:ℝ)≤3/4) (by norm_num : (3:ℝ)/4<1)
  refine ⟨c,C,hc,hC,?_⟩
  let v : ℝ := (a+b+1)/2
  let B : ℝ := 100+10*|v|+10*max s 1
  have he := (tendsto_natCast_atTop_atTop : Tendsto (fun n:ℕ => (n:ℝ)) atTop atTop).eventually
    (eventually_ge_atTop B)
  filter_upwards [he] with n hn
  have hv0 := neg_abs_le v
  have hv1 := le_abs_self v
  have hs1 : 1≤max s 1 := le_max_right _ _
  have hf : jacobi.Jacobi.frequency a b n=(n:ℝ)+v := rfl
  have hf1 : 1≤ jacobi.Jacobi.frequency a b n := by rw [hf]; dsimp [B] at hn; linarith
  constructor
  · intro m hm
    have hmr : 2*(m:ℝ)≤(n:ℝ)+6 := by exact_mod_cast hm
    exact hbound _ hf1 m ((div_le_iff₀ (by linarith : 0< jacobi.Jacobi.frequency a b n)).mpr (by
      rw [hf]; dsimp [B] at hn; linarith))
  · intro m hm
    have hmr : (m:ℝ)≤(n:ℝ)+3 := by exact_mod_cast hm
    have h := hbound (2* jacobi.Jacobi.frequency a b n) (by linarith) m
      ((div_le_iff₀ (by linarith : 0<2* jacobi.Jacobi.frequency a b n)).mpr (by
        rw [hf]; dsimp [B] at hn; linarith))
    have hstep : π/(2* jacobi.Jacobi.frequency a b n)=step a b n/2 := by dsimp [step]; ring
    rwa [hstep] at h

end
end jacobi.Support
