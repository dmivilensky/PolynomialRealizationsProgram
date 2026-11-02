import jacobi.GelfandLevitan.RegularizedKernel
import jacobi.Reference.LogMajorant

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
The genuine derivative of each original regularized term has the
printed uniform summable logarithmic inverse-square bound, on every
closed first-coordinate strip away from the singular endpoint.
Use: regularizedSlope_uniform_limit and the derivative theorem for the original F-flat series use this proved genuine majorant.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual regularized spectral derivatives obey the printed summable tail bound uniformly on every physical strip away from zero.
Use: regularizedSlope_uniform_limit and the derivative theorem for the original F-flat series use this proved genuine majorant.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: use the exact differentiated tensor decomposition, the refined original rho asymptotic and the sharp genuine spectral solution and slope differences. The original positive reference norm cancels the common squared amplitude scale; log(k+2)>=log(2)>0 absorbs the remaining inverse-square term. -/
theorem regularizedSlopeTerm_tail_bound {a d : ℝ} (ha : -1<a) (hd : 0<d) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ k : ℕ in atTop,∀ t∈Icc d (1/2),∀ s∈Icc (0:ℝ) (1/2),
      |regularizedSlopeTerm a ha k t s|≤C*Real.log (k+2:ℝ)/(k+1:ℝ)^2 := by
  -- All estimates concern the same two original spectra and the same independently defined norming data.
  obtain ⟨A,_B,hA,_hB,hsolutions⟩ := spectral_solution_bounds ha
  obtain ⟨D,hD,hslopes⟩ := spectral_slope_bounds ha hd
  obtain ⟨B,hB,hdifferences⟩ := spectral_solution_difference_sharp ha
  obtain ⟨E,hE,hslopeDifferences⟩ := spectral_slope_difference_sharp ha hd
  obtain ⟨R,hR,M,hremainders⟩ := normingRatio_asymptotic ha
  obtain ⟨_U,V,_hU,hV,hphase⟩ := displacement_phase_bounds ha
  obtain ⟨c,_C,hc,_hC,hnorm⟩ := norming_bounds ha
  let W : ℝ := 1+|displacementMass a ha| * V
  have hW : 0<W := by dsimp [W]; positivity
  let T : ℝ := E*A+D*B
  have hT : 0<T := by dsimp [T]; positivity
  let C : ℝ := R*D*A+W*T/Real.log 2
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C/c,by positivity,?_⟩
  filter_upwards [hsolutions,hslopes,hdifferences,hslopeDifferences,eventually_ge_atTop M]
    with k hsol hslope hdiff hslopeDiff hk t ht s hs
  have hkp : 0<(k+1:ℝ) := by positivity
  have hK : 1≤(k+1:ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hlog : Real.log 2≤Real.log (k+2:ℝ) := Real.log_le_log (by norm_num) (by nlinarith [Nat.cast_nonneg (α := ℝ) k])
  have hlogpos : 0<Real.log (k+2:ℝ) := hlog2.trans_le hlog
  let p : ℝ := (k+1:ℝ)^(-gamma a)
  have hp : 0<p := Real.rpow_pos_of_pos hkp _
  have hpsq : p^2=1/(k+1:ℝ)^(2*gamma a) := by
    dsimp [p]
    rw [Real.rpow_neg hkp.le,show 2*gamma a=gamma a*2 by ring,Real.rpow_mul hkp.le,
      Real.rpow_two,inv_pow,one_div]
  have hN : c*p^2≤norming a k := by rw [hpsq]; simpa only [mul_one_div] using (hnorm k).1
  have hslopescale : (k+1:ℝ)^(1-gamma a)=(k+1:ℝ)*p := by
    dsimp [p]
    rw [show 1-gamma a=-gamma a+1 by ring,Real.rpow_add_one hkp.ne']
    ring
  have hst : |realSlope a (jacobi.Bessel.sigma a ha k) t|≤D*(k+1:ℝ)*p := by
    simpa only [hslopescale,mul_assoc] using (hslope t ht).1
  have htt : |realSlope a (eigenvalue a k) t|≤D*(k+1:ℝ)*p := by
    simpa only [hslopescale,mul_assoc] using (hslope t ht).2
  have hfs : |realSolution a (jacobi.Bessel.sigma a ha k) s|≤A*p := (hsol s hs).1
  have hds : |realSolution a (jacobi.Bessel.sigma a ha k) s-realSolution a (eigenvalue a k) s|≤B*p/(k+1:ℝ)^3 := hdiff s hs
  have hdt : |realSlope a (jacobi.Bessel.sigma a ha k) t-realSlope a (eigenvalue a k) t|≤E*p/(k+1:ℝ)^2 := hslopeDiff t ht
  have hw : |1+displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2|≤W := by
    have hh : 1/(jacobi.Bessel.phaseGrid a k)^2≤V :=
      (hphase k).2.trans (div_le_self hV.le (by nlinarith))
    calc
      _ ≤ |(1:ℝ)|+|displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2| := abs_add_le _ _
      _ = 1+|displacementMass a ha| * (1/(jacobi.Bessel.phaseGrid a k)^2) := by
        rw [abs_one,abs_div,abs_of_nonneg (sq_nonneg (jacobi.Bessel.phaseGrid a k))]
        ring
      _ ≤ _ := by
        dsimp [W]
        linarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (displacementMass a ha))]
  have hrem := hremainders k hk
  have htensor : |(realSlope a (jacobi.Bessel.sigma a ha k) t-realSlope a (eigenvalue a k) t)*
        realSolution a (jacobi.Bessel.sigma a ha k) s+
      realSlope a (eigenvalue a k) t*(realSolution a (jacobi.Bessel.sigma a ha k) s-realSolution a (eigenvalue a k) s)|≤
      T*p^2/(k+1:ℝ)^2 := by
    calc
      _ ≤ |(realSlope a (jacobi.Bessel.sigma a ha k) t-realSlope a (eigenvalue a k) t)*
          realSolution a (jacobi.Bessel.sigma a ha k) s|+
        |realSlope a (eigenvalue a k) t*(realSolution a (jacobi.Bessel.sigma a ha k) s-realSolution a (eigenvalue a k) s)| := abs_add_le _ _
      _ ≤ (E*p/(k+1:ℝ)^2)*(A*p)+(D*(k+1:ℝ)*p)*(B*p/(k+1:ℝ)^3) := by
        simp only [abs_mul]
        gcongr
      _ = _ := by dsimp [T]; field_simp [hkp.ne']
  rw [regularizedSlopeTerm_decomposition,abs_div,abs_of_pos (norming_pos ha k)]
  have hnum : |(normingRatio a ha k-1-displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2)*
        realSlope a (jacobi.Bessel.sigma a ha k) t*realSolution a (jacobi.Bessel.sigma a ha k) s+
      (1+displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2)*
        ((realSlope a (jacobi.Bessel.sigma a ha k) t-realSlope a (eigenvalue a k) t)*realSolution a (jacobi.Bessel.sigma a ha k) s+
          realSlope a (eigenvalue a k) t*(realSolution a (jacobi.Bessel.sigma a ha k) s-realSolution a (eigenvalue a k) s))|≤
      C*Real.log (k+2:ℝ)*p^2/(k+1:ℝ)^2 := by
    calc
      _ ≤ |(normingRatio a ha k-1-displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2)*
          realSlope a (jacobi.Bessel.sigma a ha k) t*realSolution a (jacobi.Bessel.sigma a ha k) s|+
        |(1+displacementMass a ha/(jacobi.Bessel.phaseGrid a k)^2)*
          ((realSlope a (jacobi.Bessel.sigma a ha k) t-realSlope a (eigenvalue a k) t)*realSolution a (jacobi.Bessel.sigma a ha k) s+
            realSlope a (eigenvalue a k) t*(realSolution a (jacobi.Bessel.sigma a ha k) s-realSolution a (eigenvalue a k) s))| := abs_add_le _ _
      _ ≤ (R*Real.log (k+2:ℝ)/(k+1:ℝ)^3)*(D*(k+1:ℝ)*p)*(A*p)+W*(T*p^2/(k+1:ℝ)^2) := by
        simp only [abs_mul]
        gcongr
      _ = (R*D*A*Real.log (k+2:ℝ)+W*T)*p^2/(k+1:ℝ)^2 := by field_simp [hkp.ne']
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg p)
        dsimp [C]
        have hh : 1≤Real.log (k+2:ℝ)/Real.log 2 := (le_div_iff₀ hlog2).mpr (by simpa only [one_mul] using hlog)
        calc
          _ = R*D*A*Real.log (k+2:ℝ)+W*T*1 := by ring
          _ ≤ R*D*A*Real.log (k+2:ℝ)+W*T*(Real.log (k+2:ℝ)/Real.log 2) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hh (mul_nonneg hW.le hT.le))
          _ = _ := by ring
  exact (div_le_div₀ (by positivity) hnum (mul_pos hc (sq_pos_of_pos hp)) hN).trans_eq
    (by field_simp [hc.ne',hp.ne',hkp.ne'])

end
end jacobi.GelfandLevitan
