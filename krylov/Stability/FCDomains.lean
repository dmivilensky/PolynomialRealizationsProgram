import krylov.Stability.AnalyticFC

/-!
Article: main_krylov, lem:U(d), genuine open domain of the actual FC cycle.
Use: discharge all actual model inverses and line denominators on one
neighborhood of each positive nonstagnating quadratic reference.
Source: actual analytic trajectory, actual positive CG Gram models and finite intersection.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- All real full-memory FC solves and searches are simultaneously defined near every active positive quadratic reference.
Use: exact staircase and trajectory differentiation have their actual algorithmic domain hypotheses discharged on a genuine neighborhood.
Article: main_krylov, lem:U(d), open domain containing the nondegenerate reference.
Proof: the proved actual trajectory makes fixed-coordinate coefficient
determinants and curvatures continuous; their true quadratic values are nonzero by actual CG model positivity and search curvature. A finite intersection gives one common neighborhood. -/
theorem quadraticFC_domains (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X)
    (hA : ∀ i, AnalyticAt ℝ (fun p => A p i) x) (hg : AnalyticAt ℝ g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient Q (g x) i≠0) :
    ∀ᶠ p in 𝓝 x, ∀ k<N,
      IsUnit (crossGram (windowImages (selectedWindow fullMemory (fcHistory fullMemory (A p) (g p) k)))
        (windowSteps (selectedWindow fullMemory (fcHistory fullMemory (A p) (g p) k)))).det ∧
      inner ℝ (fcDirection fullMemory (A p) (g p) k) (A p k (fcDirection fullMemory (A p) (g p) k))≠0 := by
  -- Every finite domain bound is obtained from the real policy and its true quadratic reference values.
  have ht := quadraticFC_prefix_analytic A g x hA hg Q hAx hQ hpos N hpre
  simp only [← Finset.mem_range]
  apply (Filter.eventually_all_finite (Finset.finite_toSet (Finset.range N))).mpr
  intro k hk
  have hk' := Finset.mem_range.mp hk
  let C := fun p => (crossGram (fun i : Fin k => fcSecant fullMemory (A p) (g p) (k-1-i.val))
    (fun i : Fin k => fcStep fullMemory (A p) (g p) (k-1-i.val))).det
  have hC : AnalyticAt ℝ C x := by
    apply analytic_matrix_det
    intro i j
    exact analytic_inner (analytic_operator_apply (hA _) (ht.2 _ (by omega)).2) (ht.2 _ (by omega)).2
  have hC0 : C x≠0 := by
    dsimp only [C]
    rw [← fullFC_conjugacy_det_array,hAx]
    have hs := fcMethod_static fullMemory Q hQ hpos (g x) (fun _ _ h => h) k
    change (fcHistory fullMemory (fun _ => Q) (g x) k).gradient=CG.gradient Q (g x) k ∧
      (fcHistory fullMemory (fun _ => Q) (g x) k).pairs=referencePairs Q (g x) k at hs
    have hl : (fcHistory fullMemory (fun _ => Q) (g x) k).records.length=k := by
      rw [← History.pairs_length,hs.2,referencePairs_length]
    have hW : selectedWindow fullMemory (fcHistory fullMemory (fun _ => Q) (g x) k)=
        (referencePairs Q (g x) k).take k := by
      change (fcHistory fullMemory (fun _ => Q) (g x) k).pairs.take
        (fcHistory fullMemory (fun _ => Q) (g x) k).records.length=_
      rw [hs.2,hl]
    rw [hW]
    exact (retainedConjugacy_posDef Q hQ hpos (g x) k k (fun i hi => hpre i (by omega))).det_pos.ne'
  have hline := analytic_inner (ht.2 k hk').1 (analytic_operator_apply (hA k) (ht.2 k hk').1)
  have hline0 : inner ℝ (fcDirection fullMemory (A x) (g x) k)
      (A x k (fcDirection fullMemory (A x) (g x) k))≠0 := by
    rw [hAx,(fullFC_reference_step Q hQ hpos (g x) k).2.1]
    exact (hpos _ (CG.invariant_line_pos Q hpos (g x) k
      (CG.invariant Q hQ hpos (g x) k (fun i hi => hpre i (by omega))) (hpre k hk')).1).ne'
  filter_upwards [hC.continuousAt.eventually_ne hC0,hline.continuousAt.eventually_ne hline0] with p hp hcurv
  refine ⟨isUnit_iff_ne_zero.mpr ?_,hcurv⟩
  rwa [fullFC_conjugacy_det_array]

end
end krylov.Stability
