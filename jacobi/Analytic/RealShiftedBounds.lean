import jacobi.Analytic.RealShiftedTransfer
import jacobi.Comparison.MainBounds

/-!
Article: jacobi, Corollary C.6.
The complete bounds concern the literal ordinary real lower limiting
infimum over every original finite Jacobi fibre. Finiteness follows from
the actual candidate limit, so no infinite-value toReal convention enters
either the definition identity or the printed Young/Keller consequence.
Use: realShiftedOptimalEnergy and realShiftedOptimalEnergy_bounds concern ordinary finite real values.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.Comparison jacobi.Finite jacobi.Variational
open scoped Topology ENNReal
attribute [local instance] Measure.Subtype.measureSpace

/-- The original shifted optimum is finite throughout its full admissible real range.
Use: realShiftedOptimalEnergy and realShiftedOptimalEnergy_bounds concern ordinary finite real values.
Article: jacobi, Corollary C.6.
Proof: the genuine shifted candidate integral is a finite real upper bound. -/
theorem shiftedOptimalEnergy_ne_top {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {w:ℝ} (hw: - jacobi.Bessel.sigma a ha 0<w) : shiftedOptimalEnergy a b ha hb w≠∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (shiftedOptimalEnergy_upper ha hb hw)

/-- The original shifted full-fibre limiting optimal energy as an ordinary real number.
Use: realShiftedOptimalEnergy_definition recovers the exact real liminf/inf formula in the article.
Article: jacobi, Appendix E.1.
-/
def realShiftedOptimalEnergy (a b:ℝ) (ha:-1<a) (hb:-1<b) (w:ℝ) : ℝ :=
  (shiftedOptimalEnergy a b ha hb w).toReal

/-- Every finite original shifted extended infimum has exactly its ordinary nonnegative real infimum.
Use: realShiftedOptimalEnergy_definition identifies the source objective without changing the original full fibre.
Article: jacobi, Appendix E.1.
Proof: all genuine candidate costs are finite and nonnegative; the
community toReal-infimum identity commutes with their complete image. -/
theorem shiftedFibreInfimum_toReal {N:ℕ} (S:Nodes N) (z:ℝ) :
    (shiftedFibreInfimum S z).toReal=
      sInf ((fun J:chebyshev2.Jacobi N => realShiftedEnergy J z/(N:ℝ)^3) ''
        {J | InFiber J S.polynomial}) := by
  rw [shiftedFibreInfimum,ENNReal.toReal_sInf _ (by
    rintro y ⟨J,_,rfl⟩
    exact ENNReal.ofReal_ne_top),Set.image_image]
  congr 1
  apply Set.image_congr
  intro J _
  apply ENNReal.toReal_ofReal
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)

/-- The original shifted real optimum is exactly the printed real liminf of full finite-fibre infima.
Use: the final real two-sided corollary bounds precisely the article's objective, not a separately prescribed limiting model.
Article: jacobi, Appendix E.1.
Proof: the genuine candidate energy limit bounds the finite shifted
infima eventually by one finite constant. Commute toReal with their
lower limit, then use the exact finite real-infimum identity. -/
theorem realShiftedOptimalEnergy_definition {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {w:ℝ} (hw: - jacobi.Bessel.sigma a ha 0<w) :
    realShiftedOptimalEnergy a b ha hb w=liminf (fun n:ℕ =>
      sInf ((fun J:chebyshev2.Jacobi (n+1) => realShiftedEnergy J
        (1+w/(2*((n:ℝ)+1)^2))/((n:ℝ)+1)^3) ''
          {J | InFiber J (jacobi.Jacobi.nodes a b ha hb (n+1)).polynomial})) atTop := by
  -- The finite upper bound is supplied by actual original candidates with all premises proved.
  have he := (realShiftedCandidate_energy_limit ha hb hw).eventually
    (Iio_mem_nhds (lt_add_one (realShiftedUpper a ha w)))
  have hbnd : ∀ᶠn:ℕ in atTop,shiftedFibreInfimum (jacobi.Jacobi.nodes a b ha hb (n+1))
      (1+w/(2*((n:ℝ)+1)^2))≤ENNReal.ofReal (realShiftedUpper a ha w+1) := by
    filter_upwards [he] with n hn
    have hi : shiftedFibreInfimum (jacobi.Jacobi.nodes a b ha hb (n+1))
        (1+w/(2*((n:ℝ)+1)^2))≤realShiftedCost (targetChain a b ha hb n)
          (1+w/(2*((n:ℝ)+1)^2)) := sInf_le ⟨_,targetChain_inFiber a b ha hb n,rfl⟩
    exact hi.trans (ENNReal.ofReal_le_ofReal (by simpa only [Nat.cast_add,Nat.cast_one] using hn.le))
  have hh := ENNReal.liminf_toReal_eq ENNReal.ofReal_ne_top hbnd
  simp only [shiftedFibreInfimum_toReal,Nat.cast_add,Nat.cast_one] at hh
  exact hh.symm

/-- The genuine shifted lower constant is finite, including both complete calibration suprema.
Use: the printed real lower bound and its separate Keller consequence preserve all original extended values faithfully.
Article: jacobi, Corollary C.6.
Proof: the complete lower bound lies below the same proved finite original optimum at beta=alpha. -/
theorem shiftedLowerConstant_ne_top {a:ℝ} (ha:-1<a)
    {w:ℝ} (hw: - jacobi.Bessel.sigma a ha 0<w) : lowerConstant (realShiftSpectrum a ha w hw)≠∞ :=
  ne_top_of_le_ne_top (shiftedOptimalEnergy_ne_top ha ha hw) (shiftedOptimalEnergy_lower ha ha hw)

/-- The literal real original full-fibre shifted optimum satisfies the complete printed two-sided bounds.
Use: this is the source's Corollary C.6 with every numerical and feasibility premise discharged.
Article: jacobi, Corollary C.6.
Proof: all original quantities are proved finite. Monotonicity of toReal
transfers the completed extended bounds, and the nonnegative original
squared-profile integral cancels ofReal on the upper side. -/
theorem realShiftedOptimalEnergy_bounds {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {w:ℝ} (hw: - jacobi.Bessel.sigma a ha 0<w) :
    (lowerConstant (realShiftSpectrum a ha w hw)).toReal≤realShiftedOptimalEnergy a b ha hb w ∧
      realShiftedOptimalEnergy a b ha hb w≤realShiftedUpper a ha w := by
  have h := shiftedOptimalEnergy_bounds ha hb hw
  refine ⟨ENNReal.toReal_mono (shiftedOptimalEnergy_ne_top ha hb hw) h.1,?_⟩
  have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top h.2
  simpa only [realShiftedOptimalEnergy,ENNReal.toReal_ofReal
    (show 0≤realShiftedUpper a ha w from integral_nonneg (fun _ => sq_nonneg _))] using hu

/-- The genuine full shifted optimum obeys both printed explicit Young and Keller lower bounds.
Use: the final particular assertion of Corollary C.6 retains the actual shifted mass, moment and first eigenvalue.
Article: jacobi, Corollary C.6.
Proof: both original calibrations lie below the same completed four-term
lower constant. Its proved finiteness makes the Keller value finite;
monotonicity of toReal and the exact printed Young identity give the real maximum. -/
theorem realShiftedOptimalEnergy_young_keller {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {w:ℝ} (hw: - jacobi.Bessel.sigma a ha 0<w) :
    max ((2*sqrt 3/5)*(5*(realShiftSpectrum a ha w hw).second/2)^(3/4:ℝ))
      ((jacobi.Keller.Kel ((realShiftSpectrum a ha w hw).value 0)
        (realShiftSpectrum a ha w hw).mass).toReal)≤realShiftedOptimalEnergy a b ha hb w := by
  -- Both explicit estimates are compared inside the same finite complete lower constant.
  let Λ := realShiftSpectrum a ha w hw
  have hlow := (realShiftedOptimalEnergy_bounds ha hb hw).1
  have hY := ENNReal.toReal_mono (shiftedLowerConstant_ne_top ha hw) (young_le_lowerConstant Λ)
  rw [ENNReal.toReal_ofReal (jacobi.Young.youngValue_nonneg Λ.second_pos.le),
    jacobi.Young.youngValue_printed Λ.second_pos.le] at hY
  have hK : jacobi.Keller.Kel (Λ.value 0) Λ.mass≤lowerConstant Λ :=
    (le_max_right _ _).trans (le_max_left _ _)
  exact max_le (hY.trans hlow)
    ((ENNReal.toReal_mono (shiftedLowerConstant_ne_top ha hw) hK).trans hlow)

end
end jacobi.EdgeResolvent
