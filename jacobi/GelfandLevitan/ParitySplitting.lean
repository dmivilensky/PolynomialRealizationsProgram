import jacobi.Reference.ParityResidueIntegral
import jacobi.GelfandLevitan.UniformKernel

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The original absolutely convergent signed kernel series has sum
zero on the full physical half square. The proof uses the genuine
contour integral, its proved vanishing limit and its exact actual
finite residue identity, with no contour or residue hypotheses left.
Use: parity_splitting identifies the actual signed series limit with the proved zero limit of the corresponding contour integrals.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter _root_.Complex jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original GL summands remain absolutely summable after the alternating spectral sign is inserted.
Use: parity_splitting identifies the actual signed series limit with the proved zero limit of the corresponding contour integrals.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the alternating real power has absolute value one, so the genuine uniform kernel majorant also bounds the signed series. -/
theorem signed_kernel_summable {a : ℝ} (ha : -1<a) {t s : ℝ}
    (ht : t∈Icc (0:ℝ) (1/2)) (hs : s∈Icc (0:ℝ) (1/2)) :
    Summable (fun k : ℕ => (-1:ℝ)^k*kernelTerm a ha k t s) := by
  apply (kernel_absolute_summable a ha ht hs).of_norm_bounded
  intro k
  simp only [Real.norm_eq_abs,abs_mul,abs_neg_one_pow,one_mul,le_refl]

/-- The actual original signed GL kernel series has sum zero at every point of the physical half square.
Use: the two parity subseries each equal one half of F, which yields the genuine half-interval tight-frame identity and the two bases used in the operator part of Proposition C.2.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the actual residue theorem identifies every sufficiently large contour integral with minus the printed nonzero kappa times the original signed partial sum. The contour integrals tend to zero by the proved absolute characteristic bound. Absolute series convergence and uniqueness of limits force its genuine sum to be zero. -/
theorem parity_splitting {a : ℝ} (ha : -1<a) {t s : ℝ}
    (ht : t∈Icc (0:ℝ) (1/2)) (hs : s∈Icc (0:ℝ) (1/2)) :
    HasSum (fun k : ℕ => (-1:ℝ)^k*kernelTerm a ha k t s) 0 := by
  -- The finite residue equality is proved for the same original integrals whose limit was estimated.
  have hsum := signed_kernel_summable ha ht hs
  let S : ℝ := ∑' k : ℕ,(-1:ℝ)^k*kernelTerm a ha k t s
  let kappa : ℂ := ((2*Real.pi^2*normConstant a:ℝ):ℂ)
  have hkappa : kappa≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity [normConstant_pos ha]))
  have hp := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hp
  have hscaled := hc.const_mul (-kappa)
  obtain ⟨M,hidentity⟩ := parity_contour_residue_identity ha
  have he : (fun m : ℕ => -kappa*((∑ k∈Finset.range (m+1),(-1:ℝ)^k*kernelTerm a ha k t s:ℝ):ℂ))
      =ᶠ[atTop] parityContourIntegral a t s := by
    filter_upwards [eventually_ge_atTop M] with m hm
    exact (hidentity m hm t ht s hs).symm
  have hl := hscaled.congr' he
  have hz : -kappa*(S:ℂ)=0 := tendsto_nhds_unique hl (parity_contour_integral_limit ha ht hs)
  have hS : S=0 := Complex.ofReal_injective ((mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hkappa))
  simpa only [show (∑' k : ℕ,(-1:ℝ)^k*kernelTerm a ha k t s)=0 from hS] using hsum.hasSum

/-- The actual alternating tsum of original kernel summands vanishes on the whole physical half square.
Use: parity half-kernel identities can rewrite the genuine tsum directly while parity_splitting retains its convergence evidence.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: take the tsum value of the proved actual HasSum identity. -/
theorem parity_splitting_tsum {a : ℝ} (ha : -1<a) {t s : ℝ}
    (ht : t∈Icc (0:ℝ) (1/2)) (hs : s∈Icc (0:ℝ) (1/2)) :
    (∑' k : ℕ,(-1:ℝ)^k*kernelTerm a ha k t s)=0 := (parity_splitting ha ht hs).tsum_eq

end
end jacobi.GelfandLevitan
