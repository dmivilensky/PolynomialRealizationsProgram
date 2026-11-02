import jacobi.GelfandLevitan.RegularizedDerivativeBound

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
The original regularized spatial derivative series converges absolutely
and uniformly on every required closed strip, including both edges in
its second coordinate and the midpoint in its first coordinate. Its
sum is continuous on the same strip.
Use: every genuine regularized derivative summand is continuous on each closed strip, so its actual uniform sum is continuous there.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual spatial slope of the original real reference solution is continuous throughout the nonsingular interval.
Use: every genuine regularized derivative summand is continuous on each closed strip, so its actual uniform sum is continuous there.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: take real parts of the independently proved derivative of the actual complex spatial slope. -/
theorem realSlope_continuousAt (a E : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    ContinuousAt (realSlope a E) t :=
  Complex.continuous_re.continuousAt.comp (solutionSlope_hasDerivAt a (E:ℂ) ht).continuousAt

/-- Each actual regularized derivative summand is continuous on the entire closed physical strip.
Use: the uniform derivative series retains continuity at s=0, at t=1/2, and along the diagonal.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the genuine slopes are continuous away from zero, while the genuine solution factors remain continuous at the second-coordinate endpoint; constant products, quotients and differences preserve continuity. -/
theorem regularizedSlopeTerm_continuousOn {a d : ℝ} (ha : -1<a) (hd : 0<d) (k : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => regularizedSlopeTerm a ha k p.1 p.2)
      (Icc d (1/2)×ˢIcc (0:ℝ) (1/2)) := by
  -- The actual slope regularity is invoked only for the first coordinate, which is separated from zero.
  intro p hp
  have ht : p.1∈Ioo (0:ℝ) 1 := ⟨hd.trans_le hp.1.1,by linarith [hp.1.2]⟩
  have hst := (realSlope_continuousAt a (jacobi.Bessel.sigma a ha k) ht).comp_of_eq continuousAt_fst rfl
  have htt := (realSlope_continuousAt a (eigenvalue a k) ht).comp_of_eq continuousAt_fst rfl
  have hss := (realSolution_continuousAt ha (jacobi.Bessel.sigma a ha k) hp.2).comp_of_eq continuousAt_snd rfl
  have hts := (realSolution_continuousAt ha (eigenvalue a k) hp.2).comp_of_eq continuousAt_snd rfl
  exact ((((continuousAt_const.mul hst).mul hss).sub (htt.mul hts)).div_const _).sub
    ((((htt.mul hts).div_const _).const_mul _)) |>.continuousWithinAt

/-- A genuine summable majorant controls every original regularized derivative index uniformly on the same physical strip.
Use: gives absolute convergence, uniform convergence and continuity of the complete original derivative series without discarding any small index.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the original tail has the proved logarithmic inverse-square bound. Every finite prefix term is bounded by compact continuity, and a sequence differing at finitely many indices from the summable tail remains summable. -/
theorem regularizedSlopeTerm_summable_majorant {a d : ℝ} (ha : -1<a) (hd : 0<d) :
    ∃ u : ℕ → ℝ,Summable u ∧ ∀ k : ℕ,∀ t∈Icc d (1/2),∀ s∈Icc (0:ℝ) (1/2),
      |regularizedSlopeTerm a ha k t s|≤u k := by
  -- Compactness supplies genuine analytic bounds for the finite prefix, rather than numerical certificates.
  obtain ⟨C,_hC,htail⟩ := regularizedSlopeTerm_tail_bound ha hd
  obtain ⟨K,hK⟩ := eventually_atTop.mp htail
  have hcompact (k : ℕ) : ∃ D : ℝ,∀ t∈Icc d (1/2),∀ s∈Icc (0:ℝ) (1/2),|regularizedSlopeTerm a ha k t s|≤D := by
    obtain ⟨D,hD⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
      (regularizedSlopeTerm_continuousOn ha hd k)
    exact ⟨D,fun t ht s hs => by simpa only [Real.norm_eq_abs] using hD (t,s) ⟨ht,hs⟩⟩
  choose D hD using hcompact
  let u : ℕ → ℝ := fun k => if k<K then D k else C*Real.log (k+2:ℝ)/(k+1:ℝ)^2
  have hm : Summable (fun k : ℕ => C*Real.log (k+2:ℝ)/(k+1:ℝ)^2) := by
    simpa only [mul_div_assoc] using logarithmic_inverse_square_summable.mul_left C
  have hu : Summable u := by
    apply (summable_nat_add_iff K).mp
    exact ((summable_nat_add_iff K).mpr hm).congr (fun k => by simp only [u,ite_eq_right (by omega : ¬k+K<K)])
  refine ⟨u,hu,fun k t ht s hs => ?_⟩
  dsimp only [u]
  split_ifs with hk
  · exact hD k t ht s hs
  · exact hK k (by omega) t ht s hs

/-- The sum of the actual regularized spatial derivative terms.
Use: regularizedKernel_hasDerivAt identifies this same genuine sum with the derivative of the original F-flat; continuity is established independently by its uniform series.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
-/
def regularizedSlope (a : ℝ) (ha : -1<a) (t s : ℝ) : ℝ :=
  ∑' k : ℕ,regularizedSlopeTerm a ha k t s

/-- The original regularized spatial derivative series converges absolutely at every physical point away from its first-coordinate singular endpoint.
Use: fixes the genuine derivative sum in the termwise derivative theorem and permits legitimate sum identities.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: specialize the proved all-index summable uniform majorant to the actual point. -/
theorem regularizedSlope_absolute_summable {a d t s : ℝ} (ha : -1<a) (hd : 0<d)
    (ht : t∈Icc d (1/2)) (hs : s∈Icc (0:ℝ) (1/2)) :
    Summable (fun k : ℕ => |regularizedSlopeTerm a ha k t s|) := by
  obtain ⟨u,hu,hbound⟩ := regularizedSlopeTerm_summable_majorant ha hd
  exact hu.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => hbound k t ht s hs)

/-- The actual natural partial sums of the regularized derivative series converge uniformly on the complete required closed strip.
Use: proves continuity of the same original derivative sum, including the boundary data needed for the GL equation.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: apply the community uniform series theorem with the proved genuine summable majorant for every index. -/
theorem regularizedSlope_uniform_limit {a d : ℝ} (ha : -1<a) (hd : 0<d) :
    TendstoUniformlyOn (fun N : ℕ => fun p : ℝ × ℝ => ∑ k∈Finset.range N,regularizedSlopeTerm a ha k p.1 p.2)
      (fun p : ℝ × ℝ => regularizedSlope a ha p.1 p.2) atTop
      (Icc d (1/2)×ˢIcc (0:ℝ) (1/2)) := by
  obtain ⟨u,hu,hbound⟩ := regularizedSlopeTerm_summable_majorant ha hd
  exact tendstoUniformlyOn_tsum_nat hu (fun k p hp => by
    simpa only [Real.norm_eq_abs] using hbound k p.1 hp.1 p.2 hp.2)

/-- The genuine regularized derivative sum is jointly continuous on each entire closed physical strip away from zero.
Use: the derivative extension theorem gives the original midpoint one-sided derivative, and the subsequent GL differentiation uses these same continuous data.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the actual continuous derivative partial sums converge uniformly on the same closed strip. -/
theorem regularizedSlope_continuousOn {a d : ℝ} (ha : -1<a) (hd : 0<d) :
    ContinuousOn (fun p : ℝ × ℝ => regularizedSlope a ha p.1 p.2)
      (Icc d (1/2)×ˢIcc (0:ℝ) (1/2)) := by
  apply (regularizedSlope_uniform_limit ha hd).continuousOn
  exact Filter.Frequently.of_forall (fun N => continuousOn_finsetSum _ (fun k _ => regularizedSlopeTerm_continuousOn ha hd k))

end
end jacobi.GelfandLevitan
