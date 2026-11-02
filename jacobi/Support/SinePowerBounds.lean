import jacobi.Support.SineCorrectionError
import jacobi.Support.RisingRatioBounds

/-!
Article: jacobi, Appendix C.3 (coefficient bounds).
Uniform arbitrary-shift sine-product power bounds follow from the
actual Gamma quotient bounds and the quantitative smooth correction.
The frequency is any positive real number, so the same constants cover
both the original support step and its half step.
Use: sineProduct_power_bounds controls the actual exponential correction uniformly over all allowed mesh indices and frequencies.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter chebyshev1.SineJacobi
open scoped Topology

/-- The genuine log-sinc correction is uniformly bounded on every original fixed compact subinterval of its smooth domain.
Use: sineProduct_power_bounds controls the actual exponential correction uniformly over all allowed mesh indices and frequencies.
Article: jacobi, Appendix C.3 (top-node polynomials).
Source: compact boundedness of a continuous function, using the already proved log-sinc smoothness from chebyshev1.
Proof: restrict the genuine smooth function to the compact interval and take a nonnegative upper bound for its actual absolute value. -/
theorem logSinc_bound {b : ℝ} (_hb:0≤b) (hb1:b<1) :
    ∃L:ℝ,0≤L ∧ ∀x∈Icc (0:ℝ) b,|logSinc x|≤L := by
  have hsub : Icc (0:ℝ) b⊆Ioo (-1:ℝ) 1 := fun x hx => ⟨by linarith [hx.1],hx.2.trans_lt hb1⟩
  obtain ⟨L,hL⟩ := isCompact_Icc.bddAbove_image (logSinc_contDiff.continuousOn.mono hsub).norm
  refine ⟨max L 0,le_max_right _ _,fun x hx => ?_⟩
  have hh : |logSinc x|≤L := by simpa only [Real.norm_eq_abs] using hL (mem_image_of_mem _ hx)
  exact hh.trans (le_max_left _ _)

/-- The actual original sine products satisfy uniform two-sided power bounds at every frequency and index whose original sine arguments stay in a fixed compact half-period.
Use: support_sineProduct_bounds specializes this directly to the full original and half-step ranges in Appendix C.3, and top-node growth uses its genuine constants.
Article: jacobi, Appendix C.3 (sine-product estimates).
Proof: the actual finite Gamma factor has global positive power bounds. The exact log-sinc correction differs from (s-1)*logSinc(m/N) by at most M*(s^2+s)*m/N^2. On the stated original mesh this is uniformly bounded; exponentiation and the exact finite factorization yield both bounds. -/
theorem sineProduct_power_bounds {s b : ℝ} (hs:0<s) (hb:0≤b) (hb1:b<1) :
    ∃c C:ℝ,0<c ∧ 0<C ∧ ∀N:ℝ,1≤N→∀m:ℕ,((m:ℝ)+max s 1)/N≤b→
      c*((m:ℝ)+1)^(s-1)≤sineProduct (π/N) s m ∧
      sineProduct (π/N) s m≤C*((m:ℝ)+1)^(s-1) := by
  -- All constants arise from actual analytic bounds; every small product index is included by the Gamma-prefix estimate.
  obtain ⟨M,hM,herr⟩ := sineCorrection_error hb hb1
  obtain ⟨L,hL,hlog⟩ := logSinc_bound hb hb1
  obtain ⟨c₀,C₀,hc₀,hC₀,hpow⟩ := risingRatio_bounds hs
  let D := M*(s^2+s)+|s-1| *L
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨c₀*exp (-D),C₀*exp D,mul_pos hc₀ (exp_pos _),mul_pos hC₀ (exp_pos _),?_⟩
  intro N hN m hmesh
  have hN0 : 0<N := by linarith
  have hm0 := Nat.cast_nonneg m (α:=ℝ)
  have hmax : 0≤max s 1 := le_trans (by norm_num : (0:ℝ)≤1) (le_max_right _ _)
  have hmn : (m:ℝ)/N≤b := (div_le_div_of_nonneg_right (by linarith) hN0.le).trans hmesh
  have hmN : (m:ℝ)≤N := by have := (div_le_iff₀ hN0).mp hmn; nlinarith
  have hsmall : (m:ℝ)/N^2≤1 := (div_le_one (sq_pos_of_pos hN0)).mpr (by nlinarith)
  have hmemb : (m:ℝ)/N∈Icc (0:ℝ) b := ⟨div_nonneg hm0 hN0.le,hmn⟩
  have hcells (j : ℕ) (hj:j<m) : ((j:ℝ)+s)/N≤b ∧ ((j:ℝ)+1)/N≤b := by
    have hjm : (j:ℝ)≤m := by exact_mod_cast hj.le
    constructor
    · exact (div_le_div_of_nonneg_right (add_le_add hjm (le_max_left _ _)) hN0.le).trans hmesh
    · exact (div_le_div_of_nonneg_right (add_le_add hjm (le_max_right _ _)) hN0.le).trans hmesh
  have hcorr : |sineCorrection N s m|≤D := by
    have he := herr N s hN0 hs.le m hcells
    have hg := hlog _ hmemb
    have hs0 : 0≤M*(s^2+s) := by positivity
    have htri := norm_add_le (sineCorrection N s m-(s-1)*logSinc ((m:ℝ)/N))
      ((s-1)*logSinc ((m:ℝ)/N))
    simp only [sub_add_cancel,Real.norm_eq_abs,abs_mul] at htri
    have ht := mul_le_mul_of_nonneg_left hsmall hs0
    have hl := mul_le_mul_of_nonneg_left hg (abs_nonneg (s-1))
    have he' : |sineCorrection N s m-(s-1)*logSinc ((m:ℝ)/N)|≤M*(s^2+s) :=
      he.trans (by simpa only [mul_div_assoc,mul_one] using ht)
    exact htri.trans (add_le_add he' hl)
  have hfac := sineProduct_correction hN0 hs m
    (fun j hj => (div_lt_one hN0).mp ((hcells j hj).1.trans_lt hb1))
    (fun j hj => (div_lt_one hN0).mp ((hcells j hj).2.trans_lt hb1))
  rw [hfac]
  have hP := (hpow m).1
  have hQ := (hpow m).2
  have hpow0 : 0≤((m:ℝ)+1)^(s-1) := (rpow_pos_of_pos (by positivity) _).le
  constructor
  · have he := exp_le_exp.mpr (abs_le.mp hcorr).1
    calc
      _ = (c₀*((m:ℝ)+1)^(s-1))*exp (-D) := by ring
      _ ≤ _ := mul_le_mul hP he (exp_pos _).le (by positivity)
  · have he := exp_le_exp.mpr (abs_le.mp hcorr).2
    calc
      _ ≤ (C₀*((m:ℝ)+1)^(s-1))*exp D := mul_le_mul hQ he (exp_pos _).le (by positivity)
      _ = _ := by ring

end
end jacobi.Support
