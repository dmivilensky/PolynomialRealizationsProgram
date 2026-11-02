import jacobi.GelfandLevitan.KernelTerm

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The actual source kernel summands have a uniform inverse-square bound.
The proof combines the original norming-product perturbation, the actual
reference solution bounds at both genuine spectra, their proved true
difference estimate and the actual positive reference squared norm.
Use: finite-prefix absorption and the p-series theorem prove uniform convergence of the actual source kernel F.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Complex Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original GL summands have a uniform summable inverse-square bound at every sufficiently large genuine original spectral index.
Use: finite-prefix absorption and the p-series theorem prove uniform convergence of the actual source kernel F.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: decompose the literal numerator into its genuine norming-weight
perturbation and two genuine spectral-solution differences. The proved
uniform bounds give one common inverse-square numerator times the
squared inverse-index amplitude. The actual reference norm has that
same squared scale and a positive lower bound, so it cancels exactly. -/
theorem kernelTerm_tail_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ k:ℕ in atTop,∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),
      |kernelTerm a ha k t s|≤C/(k+1:ℝ)^2 := by
  -- Every input is an unconditional proved estimate for the actual original source data.
  obtain ⟨A,B,hA,hB,hsolutions⟩ := spectral_solution_bounds ha
  obtain ⟨_,_,D,_,_,hD,hrho⟩ := normingRatio_bounds ha
  obtain ⟨c,_,hc,_,hnorm⟩ := norming_bounds ha
  refine ⟨(D*A^2+2*A*B)/c,by positivity,?_⟩
  filter_upwards [hsolutions] with k hk t ht s hs
  obtain ⟨hbt,hrt,hdt⟩ := hk t ht
  obtain ⟨hbs,hrs,hds⟩ := hk s hs
  have hweight := (hrho k).2.2
  let p : ℝ := (k+1:ℝ)^(-gamma a)
  have hkp : 0<(k+1:ℝ) := by positivity
  have hp : 0<p := Real.rpow_pos_of_pos hkp _
  have hpsq : p^2=1/(k+1:ℝ)^(2*gamma a) := by
    dsimp [p]
    rw [Real.rpow_neg hkp.le,show 2*gamma a=gamma a*2 by ring,Real.rpow_mul hkp.le,
      Real.rpow_two,inv_pow,one_div]
  have hN : c*p^2≤norming a k := by
    rw [hpsq]
    simpa only [mul_one_div] using (hnorm k).1
  have hnum : |normingRatio a ha k*realSolution a (jacobi.Bessel.sigma a ha k) t*
        realSolution a (jacobi.Bessel.sigma a ha k) s-
      realSolution a (eigenvalue a k) t*realSolution a (eigenvalue a k) s|≤
        ((D*A^2+2*A*B)*p^2)/(k+1:ℝ)^2 := by
    have he : normingRatio a ha k*realSolution a (jacobi.Bessel.sigma a ha k) t*
          realSolution a (jacobi.Bessel.sigma a ha k) s-
        realSolution a (eigenvalue a k) t*realSolution a (eigenvalue a k) s=
        (normingRatio a ha k-1)*realSolution a (jacobi.Bessel.sigma a ha k) t*
          realSolution a (jacobi.Bessel.sigma a ha k) s+
        (realSolution a (jacobi.Bessel.sigma a ha k) t-realSolution a (eigenvalue a k) t)*
          realSolution a (jacobi.Bessel.sigma a ha k) s+
        realSolution a (eigenvalue a k) t*
          (realSolution a (jacobi.Bessel.sigma a ha k) s-realSolution a (eigenvalue a k) s) := by ring
    rw [he]
    calc
      _ ≤ |(normingRatio a ha k-1)*realSolution a (jacobi.Bessel.sigma a ha k) t*
          realSolution a (jacobi.Bessel.sigma a ha k) s|+
        |(realSolution a (jacobi.Bessel.sigma a ha k) t-realSolution a (eigenvalue a k) t)*
          realSolution a (jacobi.Bessel.sigma a ha k) s|+
        |realSolution a (eigenvalue a k) t*
          (realSolution a (jacobi.Bessel.sigma a ha k) s-realSolution a (eigenvalue a k) s)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (D/(k+1:ℝ)^2)*(A*p)*(A*p)+(B*p/(k+1:ℝ)^2)*(A*p)+
          (A*p)*(B*p/(k+1:ℝ)^2) := by
        simp only [abs_mul]
        dsimp only [p]
        gcongr
      _ = _ := by ring
  rw [kernelTerm,abs_div,abs_of_pos (norming_pos ha k)]
  have hh := div_le_div₀ (show 0≤((D*A^2+2*A*B)*p^2)/(k+1:ℝ)^2 by positivity)
    hnum (mul_pos hc (sq_pos_of_pos hp)) hN
  exact hh.trans_eq (by field_simp [hc.ne',hp.ne',hkp.ne'])

end
end jacobi.GelfandLevitan
