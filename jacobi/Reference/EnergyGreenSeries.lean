import jacobi.Reference.EnergyWronskian
import jacobi.Reference.ContinuousExpansion

/-!
Article: jacobi, Proposition C.4.
The original spectral Green series converges absolutely and uniformly
on the full closed physical square at every E<tau_1. It is continuous,
symmetric and zero on the boundary. The existing c_0 estimates and
genuine eigenfunction parity supply the same summable all-index bound.
Use: energyGreenKernel is the original spectral resolvent kernel, with E=0 giving the series printed in Appendix C.5.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual reference spectral Green summand at the real energy E.
Use: energyGreenKernel is the original spectral resolvent kernel, with E=0 giving the series printed in Appendix C.5.
Article: jacobi, Proposition C.4.
-/
def energyGreenTerm (a E : ℝ) (k : ℕ) (t s : ℝ) : ℝ :=
  eigenfunction a k t*eigenfunction a k s/(norming a k*(eigenvalue a k-E))

/-- The original spectral Green kernel at any real energy E.
Use: energyGreen_factorization identifies this same full series with the selected left/right factor at zero energy.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def energyGreenKernel (a E t s : ℝ) : ℝ := ∑' k : ℕ,energyGreenTerm a E k t s

/-- A genuine reference spectral Green summand is continuous in both physical coordinates.
Use: the full uniformly convergent original spectral expansion gives continuous Green kernels up to all boundary points.
Article: jacobi, Proposition C.4.
Proof: the actual eigenfunctions are continuous and the energy denominator is constant in space. -/
theorem energyGreenTerm_continuous {a : ℝ} (ha : -1<a) (E : ℝ) (k : ℕ) :
    Continuous (fun p : ℝ × ℝ => energyGreenTerm a E k p.1 p.2) :=
  (((eigenfunction_properties ha k).1.comp continuous_fst).mul
    ((eigenfunction_properties ha k).1.comp continuous_snd)).div_const _

/-- One summable inverse-square majorant bounds every actual Green term on the entire closed physical square below the first reference eigenvalue.
Use: energyGreen_uniform_limit and the full continuous-row norm series have all tails and finite indices controlled for the source's zero-energy kernel.
Article: jacobi, Proposition C.4.
Proof: reflect the earlier c_0 estimate into both full coordinates. The exact ratio of the old and new energy denominators is bounded by 1+|E-c_0|/(tau_1-E), so the already proved inverse-square majorant is retained. -/
theorem energyGreenTerm_uniform_bound {a E : ℝ} (ha : -1<a) (hE : E<eigenvalue a 0) :
    ∃ B : ℝ,0<B ∧ ∀ k : ℕ,∀ t∈Icc (0:ℝ) 1,∀ s∈Icc (0:ℝ) 1,
      |energyGreenTerm a E k t s|≤B/(k+1:ℝ)^2 := by
  -- The common factor depends on the actual spectral gap at E, with no finite-index exclusions.
  obtain ⟨B,hB,hbound⟩ := zeroGreenTerm_full_bound ha
  have hb (k : ℕ) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) :
      |zeroGreenTerm a k t s|≤B/(k+1:ℝ)^2 := by
    by_cases hh : s≤1/2
    · exact hbound k t ht s ⟨hs.1,hh⟩
    · have hr : 1-s∈Icc (0:ℝ) (1/2) := ⟨by linarith [hs.2],by linarith⟩
      have he : |zeroGreenTerm a k t s|=|zeroGreenTerm a k t (1-s)| := by
        simp only [zeroGreenTerm,abs_div,abs_mul,realSolution_at_reference,eigenfunction_abs_reflection ha]
      exact he.trans_le (hbound k t ht (1-s) hr)
  let C := 1+|E- jacobi.Jacobi.endpointCorrection a|/(eigenvalue a 0-E)
  have hg0 := energy_gap_pos ha hE 0
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨B*C,by positivity,fun k t ht s hs => ?_⟩
  have hg := energy_gap_pos ha hE k
  have hlo : eigenvalue a 0-E≤eigenvalue a k-E := by
    linarith [(eigenvalue_strictMono ha).monotone (Nat.zero_le k)]
  have hratio : (jacobi.Bessel.phaseGrid a k)^2/(eigenvalue a k-E)≤C := by
    have hid : (jacobi.Bessel.phaseGrid a k)^2/(eigenvalue a k-E)=
        1+(E- jacobi.Jacobi.endpointCorrection a)/(eigenvalue a k-E) := by
      rw [← reference_energy_phase]
      field_simp [hg.ne']
      ring
    rw [hid]
    have h := (div_le_div_of_nonneg_right (le_abs_self (E- jacobi.Jacobi.endpointCorrection a)) hg.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hg0 hlo)
    dsimp only [C]
    linarith
  have he : energyGreenTerm a E k t s=zeroGreenTerm a k t s*
      ((jacobi.Bessel.phaseGrid a k)^2/(eigenvalue a k-E)) := by
    simp only [energyGreenTerm,zeroGreenTerm,realSolution_at_reference]
    field_simp [(norming_pos ha k).ne',hg.ne',(jacobi.Bessel.phaseGrid_pos ha k).ne']
  rw [he,abs_mul,abs_of_nonneg (div_nonneg (sq_nonneg _) hg.le)]
  exact (mul_le_mul (hb k t ht s hs) hratio (by positivity) (by positivity)).trans_eq (by ring)

/-- The genuine original Green series converges absolutely at every point of the full closed physical square.
Use: energyGreen_factorization and endpoint limits concern an actual absolutely convergent spectral expansion.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the proved all-index bound is a constant multiple of the already verified summable inverse-square sequence. -/
theorem energyGreen_absolute_summable {a E t s : ℝ} (ha : -1<a) (hE : E<eigenvalue a 0)
    (ht : t∈Icc (0:ℝ) 1) (hs : s∈Icc (0:ℝ) 1) :
    Summable (fun k : ℕ => |energyGreenTerm a E k t s|) := by
  obtain ⟨B,_hB,hbound⟩ := energyGreenTerm_uniform_bound ha hE
  have hm : Summable (fun k : ℕ => B/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left B
  exact hm.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => hbound k t ht s hs)

/-- The original Green partial sums converge uniformly on the entire closed physical square at every energy below tau_1.
Use: the zero-energy factorization has the full boundary-inclusive uniform convergence required by Appendix C.5, not only half-square or pointwise convergence.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: apply the community uniform-series theorem with the proved common inverse-square majorant. -/
theorem energyGreen_uniform_limit {a E : ℝ} (ha : -1<a) (hE : E<eigenvalue a 0) :
    TendstoUniformlyOn (fun N : ℕ => fun p : ℝ × ℝ =>
      ∑ k∈Finset.range N,energyGreenTerm a E k p.1 p.2)
      (fun p => energyGreenKernel a E p.1 p.2) atTop
      (Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1) := by
  obtain ⟨B,_hB,hbound⟩ := energyGreenTerm_uniform_bound ha hE
  have hm : Summable (fun k : ℕ => B/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left B
  exact tendstoUniformlyOn_tsum_nat hm (fun k p hp => by
    simpa only [Real.norm_eq_abs] using hbound k p.1 hp.1 p.2 hp.2)

/-- The genuine spectral Green kernel is continuous on the full closed physical square.
Use: once the original selected factor is identified pointwise, its joint boundary continuity follows without an assumption about its singular opposite-end behavior.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the original continuous finite sums converge uniformly on the same closed square. -/
theorem energyGreenKernel_continuousOn {a E : ℝ} (ha : -1<a) (hE : E<eigenvalue a 0) :
    ContinuousOn (fun p : ℝ × ℝ => energyGreenKernel a E p.1 p.2)
      (Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1) := by
  apply (energyGreen_uniform_limit ha hE).continuousOn
  exact Filter.Frequently.of_forall (fun N =>
    continuousOn_finsetSum _ (fun k _ => (energyGreenTerm_continuous ha E k).continuousOn))

/-- The original Green kernel is symmetric in its physical arguments.
Use: supplies the source's self-adjoint real kernel in Appendix C.5 before identification with its selected-solution factor.
Article: jacobi, Proposition C.4.
Proof: commute the two actual eigenfunction factors in each original spectral term. -/
theorem energyGreenKernel_symmetric (a E t s : ℝ) :
    energyGreenKernel a E t s=energyGreenKernel a E s t := by
  unfold energyGreenKernel energyGreenTerm
  congr 1
  funext k
  rw [mul_comm (eigenfunction a k t)]

/-- Every original spectral Green summand is a continuous full-interval row.
Use: energyGreenRowTerm_summable and its true L2 image compare the uniform Green series with the original complete reference Hilbert expansion.
Article: jacobi, Proposition C.4.
-/
def energyGreenRowTerm (a E : ℝ) (ha : -1<a) (k : ℕ) (s : ℝ) : C(Interval,ℝ) :=
  ⟨fun t => energyGreenTerm a E k t s,by
    exact ((((eigenfunction_properties ha k).1.comp continuous_subtype_val).mul continuous_const).div_const _)⟩

/-- The actual Green row series converges in the original full-interval continuous-function norm.
Use: energyGreen_factorization maps the same true norm-convergent series into the already constructed complete reference Hilbert space.
Article: jacobi, Proposition C.4.
Proof: the proved whole-square bound controls the actual supremum norm of each original row term. -/
theorem energyGreenRowTerm_summable {a E s : ℝ} (ha : -1<a) (hE : E<eigenvalue a 0)
    (hs : s∈Icc (0:ℝ) 1) : Summable (fun k : ℕ => energyGreenRowTerm a E ha k s) := by
  obtain ⟨B,_hB,hbound⟩ := energyGreenTerm_uniform_bound ha hE
  have hm : Summable (fun k : ℕ => B/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left B
  exact hm.of_norm_bounded (fun k => (ContinuousMap.norm_le _ (by positivity)).mpr
    (fun t => by change |energyGreenTerm a E k t s|≤_; exact hbound k t t.property s hs))

/-- The continuous Green row series maps to its genuine reference basis expansion term by term.
Use: energyGreen_factorization identifies the original selected factor by computing these same coefficients in the complete actual Hilbert basis.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: each true row term is its actual scalar coefficient times the already embedded original continuous eigenfunction; use linearity of the L2 embedding. -/
theorem energyGreenRowTerm_toLp (a E : ℝ) (ha : -1<a) (k : ℕ) (s : ℝ) :
    ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (energyGreenRowTerm a E ha k s)=
      (eigenfunction a k s/(norming a k*(eigenvalue a k-E))) • waveVector a ha k := by
  have he : energyGreenRowTerm a E ha k s=
      (eigenfunction a k s/(norming a k*(eigenvalue a k-E))) • continuousEigenfunction a ha k := by
    ext t
    change energyGreenTerm a E k t s=_
    simp only [energyGreenTerm,ContinuousMap.smul_apply,smul_eq_mul,continuousEigenfunction,ContinuousMap.coe_mk]
    ring
  rw [he,map_smul,continuousEigenfunction_toLp]

end
end jacobi.Reference
