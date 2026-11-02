import jacobi.Reference.NormingFormula
import jacobi.Reference.GammaRatio

/-!
Article: jacobi, Lemma C.1.
The original norming integrals have their exact leading power-law limit
and globally uniform two-sided power bounds, including every small
index. Euler's community Gamma limit supplies the actual asymptotic;
positivity absorbs the finite original prefix without numerical checks.
Use: supplies the genuine uniform norm scale in the original GL kernel estimates, with all special-function asymptotic inputs proved.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual reference squared norm has exactly the source's leading power-law constant.
Use: supplies the genuine uniform norm scale in the original GL kernel estimates, with all special-function asymptotic inputs proved.
Article: jacobi, Lemma C.1.
Proof: substitute the proved actual Gamma norm. Its normalized ratio is
the genuine Euler Gamma ratio times two elementary fixed-shift degree
ratios. The exact community Gamma limit and positive real-power
continuity evaluate their product. -/
theorem norming_asymptotic {a : ℝ} (ha : -1<a) :
    Tendsto (fun k : ℕ => norming a k*(k+1:ℝ)^(2*gamma a)) atTop (𝓝 (normConstant a)) := by
  -- The leading constant comes from the actual norm integral and genuine Gamma limit, rather than a separately assumed Stirling formula.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hR := gamma_ratio_limit (show 0<2*gamma a by positivity)
  have hS := shifted_nat_ratio (2*gamma a) (gamma a)
  have hP := (shifted_nat_ratio 1 0).rpow_const (p := 2*gamma a) (Or.inl one_ne_zero)
  simp only [add_zero,Real.one_rpow] at hP
  have h := ((hR.mul hS).mul hP).const_mul (normConstant a)
  simp only [mul_one] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hkg : 0<(k:ℝ)+gamma a := by positivity
  have hks : 0<(k:ℝ)+2*gamma a := by positivity
  rw [norming_formula ha,Real.div_rpow (by positivity : (0:ℝ)≤k+1) hkR.le]
  field_simp [hkR.ne',hkg.ne',hks.ne',
    (Real.Gamma_pos_of_pos hks).ne',(Real.rpow_pos_of_pos hkR (2*gamma a)).ne']

/-- Every actual original reference norm satisfies uniform positive two-sided source power bounds at every index.
Use: supplies both denominator and normalized-wave bounds in the genuine original GL kernel estimates.
Article: jacobi, Lemma C.1.
Proof: the actual normalized norms tend to the proved positive leading
constant. The genuine norms are positive at every original small index;
the existing finite-prefix lower lemma and a finite positive upper sum
give common constants. Divide by the actual positive index power. -/
theorem norming_bounds {a : ℝ} (ha : -1<a) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ k : ℕ,
      c/(k+1:ℝ)^(2*gamma a)≤norming a k ∧ norming a k≤C/(k+1:ℝ)^(2*gamma a) := by
  -- Every original small index is absorbed through its actual positive norm; no finite numerical prefix certificate is used.
  let f := fun k : ℕ => norming a k*(k+1:ℝ)^(2*gamma a)
  have hf : ∀ k,0<f k := fun k => mul_pos (norming_pos ha k) (Real.rpow_pos_of_pos (by positivity) _)
  have hA := normConstant_pos ha
  have hlim := norming_asymptotic ha
  have hlower : ∀ᶠ k : ℕ in atTop,normConstant a/2≤f k := by
    exact (hlim.eventually (Ioi_mem_nhds (show normConstant a/2<normConstant a by linarith))).mono (fun _ h => h.le)
  obtain ⟨c,hc,hlo⟩ := jacobi.Bessel.positive_lower_all hf (show 0<normConstant a/2 by positivity) hlower
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    ((hlim.eventually (Iio_mem_nhds (show normConstant a<normConstant a+1 by linarith))).mono (fun _ h => h.le))
  let C := normConstant a+1+∑ k∈Finset.range K,f k
  have hsum : 0≤∑ k∈Finset.range K,f k := Finset.sum_nonneg (fun k _ => (hf k).le)
  have hC : 0<C := by dsimp [C]; linarith
  refine ⟨c,C,hc,hC,?_⟩
  intro k
  have hp : 0<(k+1:ℝ)^(2*gamma a) := Real.rpow_pos_of_pos (by positivity) _
  constructor
  · exact (div_le_iff₀ hp).mpr (by simpa only [f,mul_comm] using hlo k)
  · apply (le_div_iff₀ hp).mpr
    change f k≤C
    by_cases hk : K≤k
    · have hh := hK k hk
      change f k≤normConstant a+1 at hh
      dsimp [C]
      linarith
    · have hh : f k≤∑ j∈Finset.range K,f j :=
        Finset.single_le_sum (fun j _ => (hf j).le) (Finset.mem_range.mpr (by omega))
      dsimp [C]
      linarith

end
end jacobi.Reference
