import jacobi.Analytic.FiniteShiftedBounds
import jacobi.Analytic.RealShiftSpectrum
import jacobi.Finite.ShiftedFibre
import jacobi.Jacobi.FibreLimit

/-!
Article: jacobi, Corollary C.6.
The genuine finite real shifted spectrum has the full L1 limit already
proved in the complex slit plane. The affine transformed contractive
fibre has precisely theta times this same finite spectrum.
Use: shiftedNodes_spectrum identifies the exact spectrum to which full Transfer applies.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter jacobi.Finite jacobi.Packing jacobi.Variational
open scoped Topology

/-- The actual finite real shifted eigenvalues, with the original zero padding.
Use: shiftedNodes_spectrum identifies the exact spectrum to which full Transfer applies.
Article: jacobi, Appendix E.1.
-/
def finiteRealShiftedEdge (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) (w:ℝ) : ℝ :=
  jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k/
    (1+ jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k/2*w)

/-- Real specialization preserves every original finite shifted spectral coefficient.
Use: finiteRealShiftedEdge_l1_limit reuses the complex compact-uniform theorem without a second spectral convergence proof.
Article: jacobi, Appendix E.1.
Proof: complexification commutes with the original real rational transform. -/
theorem finiteRealShiftedEdge_cast (a b:ℝ) (ha:-1<a) (hb:-1<b) (n k:ℕ) (w:ℝ) :
    (finiteRealShiftedEdge a b ha hb n k w:ℂ)=finiteShiftedEdge a b ha hb n k (w:ℂ) := by
  unfold finiteRealShiftedEdge finiteShiftedEdge resolventTransform
  push_cast
  rfl

/-- The entire actual real shifted finite spectrum converges in L1 on the full admissible real range.
Use: the affine-fibre lower bound needs the same original shifted spectrum, not just convergence of finitely many nodes.
Article: jacobi, Appendix E.1.
Proof: specialize the already proved compact-uniform complex L1 estimate
to the original real singleton. Norms of the complexified real differences
are exactly the original real absolute errors. -/
theorem finiteRealShiftedEdge_l1_limit {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {w:ℝ} (hw: - jacobi.Bessel.sigma a ha 0<w) :
    Tendsto (fun n:ℕ => distance (fun k => finiteRealShiftedEdge a b ha hb n k w)
      (realShiftedEdge a ha w)) atTop (𝓝 0) := by
  -- The singleton is inside the genuine slit domain by the strict original first-pole condition.
  have h := finiteShiftedEdge_l1_uniform ha hb (W:={(w:ℂ)}) isCompact_singleton
    (by intro z hz; rw [mem_singleton_iff.mp hz]; exact Or.inr hw)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N,hN⟩ := h ε hε
  refine ⟨N,fun n hn => ?_⟩
  have hh := hN n hn (w:ℂ) (mem_singleton _)
  have he (k:ℕ) : shiftedEdge a ha k (w:ℂ)=(realShiftedEdge a ha w k:ℂ) := by
    simp only [shiftedEdge,realShiftedEdge,Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_ofNat]
  simp only [← finiteRealShiftedEdge_cast,he,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hh
  rw [Real.dist_eq,sub_zero]
  change |(∑'k,|finiteRealShiftedEdge a b ha hb n k w-realShiftedEdge a ha w k|)| < ε
  rw [abs_of_nonneg (tsum_nonneg (fun k => abs_nonneg
    (finiteRealShiftedEdge a b ha hb n k w-realShiftedEdge a ha w k)))]
  exact hh

/-- The actual edge points tend to the original endpoint one.
Use: the genuine affine energy and spectral normalization factors tend to one.
Article: jacobi, Appendix E.1.
Proof: the reciprocal square of the actual matrix dimension tends to zero. -/
theorem real_edgePoint_limit (w:ℝ) :
    Tendsto (fun n:ℕ => 1+w/(2*((n:ℝ)+1)^2)) atTop (𝓝 1) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).pow 2
  have he : (fun n:ℕ => 1+w/(2*((n:ℝ)+1)^2))=
      (fun n:ℕ => 1+(w/2)*(1/((n:ℝ)+1))^2) := by ext n; field_simp
  rw [he]
  simpa only [zero_pow (by decide: (2:ℕ)≠0),mul_zero,add_zero] using (h.const_mul (w/2)).const_add 1

/-- The actual source affine factors tend to one, including negative admissible shifts.
Use: shifted-fibre spectral and energy limits remove the original theta_N normalization.
Article: jacobi, Appendix E.1.
Proof: max and the original affine formula are continuous at z=1. -/
theorem shiftScale_limit (w:ℝ) :
    Tendsto (fun n:ℕ => shiftScale (1+w/(2*((n:ℝ)+1)^2))) atTop (𝓝 1) := by
  have hc : Continuous shiftScale := by unfold shiftScale shiftTranslation; fun_prop
  have h := hc.continuousAt.tendsto.comp (real_edgePoint_limit w)
  have he : shiftScale 1=1 := by norm_num [shiftScale,shiftTranslation]
  simpa only [he,Function.comp_def] using h

/-- The transformed contractive fibre has theta times the exact original shifted finite spectrum.
Use: the lower bound applies full Transfer with the genuine limiting real shifted edge spectrum.
Article: jacobi, Appendix E.1.
Proof: before the original dimension cutoff, substitute the actual
Jacobi reciprocal-node formula and the source's literal affine nodes.
Every original dimension and spectral gap is nonzero. After the cutoff,
both genuine padded sequences vanish exactly. -/
theorem shiftedNodes_spectrum (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (w:ℝ)
    (hz:0<1+w/(2*((n:ℝ)+1)^2))
    (ht:∀k,(jacobi.Jacobi.nodes a b ha hb (n+1)).value k<1+w/(2*((n:ℝ)+1)^2)) :
    fibreSpectrum (shiftedNodes (jacobi.Jacobi.nodes a b ha hb (n+1)) _ hz ht)=
      fun k => shiftScale (1+w/(2*((n:ℝ)+1)^2))*finiteRealShiftedEdge a b ha hb n k w := by
  -- The same finite zero padding is essential for the full L1 comparison.
  funext k
  by_cases hk:k<n+1
  · rw [fibreSpectrum,dite_eq_left hk,finiteRealShiftedEdge,
      jacobi.Jacobi.finiteLambdaAt_eq ha hb hk,jacobi.Jacobi.finiteLambda_node ha hb ⟨k,hk⟩]
    dsimp only [nodeResolvent,shiftedNodes]
    push_cast
    have htheta := (shiftScale_pos hz).ne'
    have hgap := (sub_pos.mpr ((jacobi.Jacobi.nodes a b ha hb (n+1)).interval ⟨k,hk⟩).2).ne'
    have hm := sub_pos.mpr (ht ⟨k,hk⟩)
    have hscale : shiftScale (1+w/(2*((n:ℝ)+1)^2))=
        1+w/(2*((n:ℝ)+1)^2)+shiftTranslation (1+w/(2*((n:ℝ)+1)^2)) := rfl
    generalize hx : (jacobi.Jacobi.nodes a b ha hb (n+1)).value ⟨k,hk⟩=x at *
    generalize hq : (n:ℝ)+1=q at *
    generalize hzv : 1+w/(2*q^2)=z at *
    have hqpos : 0<q := by rw [← hq]; positivity
    have hg : 1-(x+shiftTranslation z)/shiftScale z=(z-x)/shiftScale z := by
      field_simp
      linarith [hscale]
    rw [hg]
    have hm' : 2*q^2*(1-x)+w≠0 := by
      apply ne_of_gt
      have hh : 0<2*q^2*(z-x) := mul_pos (by positivity) hm
      rw [← hzv] at hh
      field_simp at hh
      nlinarith
    have hm2 : q^2*(1-x)*2+w≠0 := by intro he; apply hm'; nlinarith [he]
    have hzpoly : 2*q^2*(z-1)=w := by rw [← hzv]; field_simp; ring
    field_simp [htheta,hgap,hm.ne',hqpos.ne',hm',hm2]
    nlinarith [hzpoly]
  · simp only [fibreSpectrum,dite_eq_right hk,finiteRealShiftedEdge,
      jacobi.Jacobi.finiteLambdaAt_zero ha hb (not_lt.mp hk),zero_div,mul_zero]

end
end jacobi.EdgeResolvent
