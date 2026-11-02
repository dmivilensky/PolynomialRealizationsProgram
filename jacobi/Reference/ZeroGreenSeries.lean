import jacobi.Reference.SpectralDisplacement
import jacobi.GelfandLevitan.UniformKernel

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
The original reference Green series at c_0 is an actual absolutely
and uniformly convergent series on the whole physical half square.
Its selected-solution factorization is a separate identification of
this already fixed series, with the independently proved Wronskian.
Use: zeroGreenKernel is the same spectral Green term subtracted in F-flat; its later factorization identifies this actual series rather than defining a separate candidate.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original reference Green-series summand at energy c_0.
Use: zeroGreenKernel is the same spectral Green term subtracted in F-flat; its later factorization identifies this actual series rather than defining a separate candidate.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def zeroGreenTerm (a : ℝ) (k : ℕ) (t s : ℝ) : ℝ :=
  (realSolution a (eigenvalue a k) t*realSolution a (eigenvalue a k) s)/
    (norming a k*(jacobi.Bessel.phaseGrid a k)^2)

/-- Each genuine reference Green summand is continuous on the full physical half square.
Use: zeroGreenKernel_continuousOn passes continuity through the proved original uniform series.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the two actual real reference solutions are continuous including zero, and their norm and phase denominators are constant in space. -/
theorem zeroGreenTerm_continuousOn {a : ℝ} (ha : -1<a) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => zeroGreenTerm a k p.1 p.2)
      (Icc (0:ℝ) (1/2)×ˢIcc (0:ℝ) (1/2)) := by
  intro p hp
  exact (((jacobi.GelfandLevitan.realSolution_continuousAt ha (eigenvalue a k) hp.1).comp_of_eq continuousAt_fst rfl).mul
    ((jacobi.GelfandLevitan.realSolution_continuousAt ha (eigenvalue a k) hp.2).comp_of_eq continuousAt_snd rfl)).div_const _ |>.continuousWithinAt

/-- The original reference Green summands have a uniform inverse-square tail bound in their genuine spectral enumeration.
Use: zeroGreenTerm_uniform_bound absorbs the actual finite prefix and supplies the summable majorant for the complete Green series.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the actual two wave amplitudes have the same squared inverse-index scale as the positive reference norm; cancel that scale and use the proved reciprocal squared phase bound. -/
theorem zeroGreenTerm_tail_bound {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ k : ℕ in atTop,∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),
      |zeroGreenTerm a k t s|≤B/(k+1:ℝ)^2 := by
  -- Every denominator estimate is for the genuine independently defined reference norm and phase.
  obtain ⟨A,_B,hA,_hB,hsolutions⟩ := spectral_solution_bounds ha
  obtain ⟨c,_C,hc,_hC,hnorm⟩ := norming_bounds ha
  obtain ⟨_D,D,_hD,hD,hphase⟩ := displacement_phase_bounds ha
  refine ⟨(A^2/c)*D,by positivity,?_⟩
  filter_upwards [hsolutions] with k hk t ht s hs
  let p : ℝ := (k+1:ℝ)^(-gamma a)
  have hkp : 0<(k+1:ℝ) := by positivity
  have hp : 0<p := Real.rpow_pos_of_pos hkp _
  have hpsq : p^2=1/(k+1:ℝ)^(2*gamma a) := by
    dsimp [p]
    rw [Real.rpow_neg hkp.le,show 2*gamma a=gamma a*2 by ring,Real.rpow_mul hkp.le,
      Real.rpow_two,inv_pow,one_div]
  have hN : c*p^2≤norming a k := by rw [hpsq]; simpa only [mul_one_div] using (hnorm k).1
  have hnum : |realSolution a (eigenvalue a k) t*realSolution a (eigenvalue a k) s|≤A^2*p^2 := by
    rw [abs_mul]
    exact (mul_le_mul (hk t ht).2.1 (hk s hs).2.1 (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hquot : |realSolution a (eigenvalue a k) t*realSolution a (eigenvalue a k) s|/norming a k≤A^2/c :=
    (div_le_div₀ (by positivity) hnum (mul_pos hc (sq_pos_of_pos hp)) hN).trans_eq (by field_simp [hc.ne',hp.ne'])
  have he : |zeroGreenTerm a k t s|=
      (|realSolution a (eigenvalue a k) t*realSolution a (eigenvalue a k) s|/norming a k)*
        (1/(jacobi.Bessel.phaseGrid a k)^2) := by
    simp only [zeroGreenTerm,abs_div,abs_mul,abs_of_pos (norming_pos ha k),abs_of_nonneg (sq_nonneg (jacobi.Bessel.phaseGrid a k))]
    ring
  rw [he]
  exact (mul_le_mul hquot (hphase k).2 (by positivity) (by positivity)).trans_eq (by ring)

/-- The genuine reference Green terms have one common inverse-square bound for all original indices and the whole half square.
Use: zeroGreen_absolute_summable and zeroGreen_uniform_limit retain every finite small-index term of the actual series.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: compact continuity bounds each finite prefix term; a finite sum of scaled bounds augments the proved inverse-square tail constant. -/
theorem zeroGreenTerm_uniform_bound {a : ℝ} (ha : -1<a) :
    ∃ B : ℝ,0<B ∧ ∀ k : ℕ,∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),
      |zeroGreenTerm a k t s|≤B/(k+1:ℝ)^2 := by
  -- The finite prefix is bounded analytically by compactness, without any finite numerical certificate.
  obtain ⟨B,hB,htail⟩ := zeroGreenTerm_tail_bound ha
  obtain ⟨K,hK⟩ := eventually_atTop.mp htail
  have hcompact (k : ℕ) : ∃ D : ℝ,0<D ∧ ∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),|zeroGreenTerm a k t s|≤D := by
    obtain ⟨D,hD⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn (zeroGreenTerm_continuousOn ha k)
    refine ⟨|D|+1,by positivity,fun t ht s hs => ?_⟩
    have hh := hD (t,s) ⟨ht,hs⟩
    rw [Real.norm_eq_abs] at hh
    linarith [le_abs_self D]
  choose D hD hDbound using hcompact
  let S : ℝ := ∑ j∈Finset.range K,D j*(j+1:ℝ)^2
  have hS : 0≤S := Finset.sum_nonneg (fun j _ => mul_nonneg (hD j).le (sq_nonneg _))
  refine ⟨B+S,by positivity,fun k t ht s hs => ?_⟩
  by_cases hk : K≤k
  · exact (hK k hk t ht s hs).trans (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _))
  · have hi : D k*(k+1:ℝ)^2≤S := Finset.single_le_sum
      (s := Finset.range K) (f := fun j => D j*(j+1:ℝ)^2)
      (fun j _ => mul_nonneg (hD j).le (sq_nonneg _)) (Finset.mem_range.mpr (by omega))
    apply (le_div_iff₀ (by positivity : 0<(k+1:ℝ)^2)).mpr
    have hm := mul_le_mul_of_nonneg_right (hDbound k t ht s hs) (sq_nonneg (k+1:ℝ))
    linarith

/-- The original reference Green kernel at c_0, defined by its actual full spectral series.
Use: the regularized kernel is F-displacementMass*zeroGreenKernel, and the later selected-solution factorization identifies this fixed original series.
Article: jacobi, Theorem 2.1.
-/
def zeroGreenKernel (a t s : ℝ) : ℝ := ∑' k : ℕ,zeroGreenTerm a k t s

/-- The original reference Green series converges absolutely at every physical half-square point.
Use: regularized_kernel_series splits the genuine F-flat series into F minus its actual Green term.
Article: jacobi, Theorem 2.1.
Proof: the all-index inverse-square bound is a genuine summable majorant. -/
theorem zeroGreen_absolute_summable {a : ℝ} (ha : -1<a) {t s : ℝ}
    (ht : t∈Icc (0:ℝ) (1/2)) (hs : s∈Icc (0:ℝ) (1/2)) :
    Summable (fun k : ℕ => |zeroGreenTerm a k t s|) := by
  obtain ⟨B,_hB,hbound⟩ := zeroGreenTerm_uniform_bound ha
  have hm : Summable (fun k : ℕ => B/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left B
  exact hm.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => hbound k t ht s hs)

/-- The actual reference Green partial sums converge uniformly on the whole physical half square.
Use: zeroGreenKernel_continuousOn and the regularized F series preserve the genuine singular-edge values and uniform continuity.
Article: jacobi, Theorem 2.1.
Proof: apply the community uniform series theorem to the proved all-index inverse-square majorant. -/
theorem zeroGreen_uniform_limit {a : ℝ} (ha : -1<a) :
    TendstoUniformlyOn (fun N : ℕ => fun p : ℝ × ℝ => ∑ k∈Finset.range N,zeroGreenTerm a k p.1 p.2)
      (fun p : ℝ × ℝ => zeroGreenKernel a p.1 p.2) atTop
      (Icc (0:ℝ) (1/2)×ˢIcc (0:ℝ) (1/2)) := by
  obtain ⟨B,_hB,hbound⟩ := zeroGreenTerm_uniform_bound ha
  have hm : Summable (fun k : ℕ => B/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left B
  exact tendstoUniformlyOn_tsum_nat hm (fun k p hp => by
    simpa only [Real.norm_eq_abs] using hbound k p.1 hp.1 p.2 hp.2)

/-- The actual reference Green kernel defined by the spectral series is continuous on the entire physical half square.
Use: F-flat is a genuine continuous regularization of the previously constructed F, before its differentiability and the Green factorization are proved.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the original continuous finite partial sums converge uniformly on the same closed square. -/
theorem zeroGreenKernel_continuousOn {a : ℝ} (ha : -1<a) :
    ContinuousOn (fun p : ℝ × ℝ => zeroGreenKernel a p.1 p.2)
      (Icc (0:ℝ) (1/2)×ˢIcc (0:ℝ) (1/2)) := by
  apply (zeroGreen_uniform_limit ha).continuousOn
  apply Filter.Frequently.of_forall
  intro N
  exact continuousOn_finsetSum _ (fun k _ => zeroGreenTerm_continuousOn ha k)

end
end jacobi.Reference
