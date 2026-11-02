import jacobi.Applications.NesterovEdge
import jacobi.Applications.NesterovZeros

/-!
Article: jacobi, Proposition A.1.
Use: nesterov_all_hard_edge and nesterov_all_small_zero_limit express the full sequence of the source proposition.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial Complex Set Filter
open scoped Topology

/-- The literal Nesterov residual indexed by its original iteration count.
Use: nesterov_all_hard_edge and nesterov_all_small_zero_limit express the full sequence of the source proposition.
Article: jacobi, Proposition A.1.
-/
def nesterovAt (b : ℝ) (k : ℕ) : Polynomial ℝ :=
  nesterovResidual b ((k-1)/2) ((k-1)%2)

/-- The original iteration index equals the exact degree/parity reconstruction at every positive count.
Use: both full-sequence limit theorems replace their parity denominators by the original k, with no asymptotic index substitution.
Article: jacobi, Proposition A.1.
Proof: Euclidean division by two gives the exact natural-number identity. -/
theorem nesterov_index {k : ℕ} (hk : 0<k) :
    2*((k-1)/2)+1+(k-1)%2=k := by omega

/-- The full iteration-index polynomial equals the original printed Nesterov Gegenbauer residual for every positive iteration count.
Use: nesterov_all_hard_edge and its ordered zeros concern exactly the residual in the source formula, including both parities and the endpoint lambda=1.
Article: jacobi, Proposition A.1.
Proof: apply the established square-root formula to the exact quotient and remainder of k-1; Euclidean division identifies both its polynomial degree and its real exponent. -/
theorem nesterovAt_sqrt_formula {b : ℝ} (hb : -1<b) {k : ℕ} (hk : 0<k)
    {l : ℝ} (hl : l≤1) :
    aeval (l:ℂ) (nesterovAt b k)=
      ((1-l)^(((k+1:ℕ):ℝ)/2):ℝ)*
        (jacobi.Jacobi.gegenbauer (((b+1)/2:ℝ):ℂ) (k-1) (Real.sqrt (1-l):ℂ)/
          jacobi.Jacobi.gegenbauer (((b+1)/2:ℝ):ℂ) (k-1) 1) := by
  have h := nesterov_sqrt_formula hb (e := (k-1)%2) (by omega) ((k-1)/2) hl
  have hd : 2*((k-1)/2)+(k-1)%2=k-1 := by omega
  have hp : 2*((k-1)/2)+2+(k-1)%2=k+1 := by omega
  rw [hd,hp] at h
  exact h

/-- The original complete Nesterov residual's interior zeros are exactly the actual increasing Jacobi zero list at its true degree and parity.
Use: nesterov_all_small_zero_limit proves the source's numbered small-zero limit for the original full residual sequence.
Article: jacobi, Proposition A.1.
Proof: substitute the exact index decomposition into the proved exhaustive interior-zero equivalence. -/
theorem nesterovAt_small_zero_iff {b : ℝ} (hb : -1<b) (k : ℕ) {x : ℝ}
    (hx : x∈Ioo (0:ℝ) 1) :
    (nesterovAt b k).eval x=0 ↔
      ∃ i : Fin ((k-1)/2),nesterovSmallZeros b hb ((k-1)%2) ((k-1)/2) i=x :=
  nesterov_small_zero_iff hb ((k-1)%2) ((k-1)/2) hx

/-- The actual Jacobi degree grows to infinity along the complete Nesterov iteration sequence.
Use: the full complex and ordered-zero limits may compose either parity's already proved theorem with this same actual degree map.
Article: jacobi, Proposition A.1.
Proof: subtraction by one and natural division by the fixed positive integer two both preserve the atTop filter. -/
theorem nesterov_degree_tendsto : Tendsto (fun k : ℕ => (k-1)/2) atTop atTop :=
  (show Tendsto (fun k : ℕ => k/2) atTop atTop from
    le_of_eq (map_div_atTop_eq_nat 2 (by omega))).comp (tendsto_sub_atTop_nat 1)

/-- Selecting between two functions with the same limit preserves their limit on any filter.
Use: the original Nesterov parity may vary with every iteration; its two proved joint limits and zero limits still imply convergence of the full sequence.
Article: jacobi, Proposition A.1.
Source: finite intersection of eventual filter properties.
Proof: eventually both functions lie in any prescribed target set; choose the appropriate one using the exhaustive parity cases zero and one. -/
theorem tendsto_parity_choice {ι X : Type*} {l : Filter ι} {L : Filter X}
    (f : ℕ → ι → X) (e : ι → ℕ) (he : ∀ i,e i≤1)
    (h0 : Tendsto (f 0) l L) (h1 : Tendsto (f 1) l L) :
    Tendsto (fun i => f (e i) i) l L := by
  -- Membership in any target filter set holds for both candidates on one common eventual set.
  refine tendsto_def.mpr (fun S hS => ?_)
  filter_upwards [h0.eventually hS,h1.eventually hS] with i hi0 hi1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (he i) with h | h
  · change f (e i) i∈S
    rw [h]
    exact hi0
  · change f (e i) i∈S
    rw [h]
    exact hi1

/-- The original full Nesterov residual sequence has the printed entire Bessel hard-edge limit locally uniformly on the complex plane.
Use: nesterov_all_hard_edge_uniform is exactly the source proposition's uniformity on complex compact sets for the complete iteration sequence.
Article: jacobi, Proposition A.1.
Proof: compose both parity joint limits with the actual growing degree map, select the actual parity, and use the exact reconstruction of k. The joint-limit criterion supplies genuine local uniformity. -/
theorem nesterov_all_hard_edge {b : ℝ} (hb : -1<b) :
    TendstoLocallyUniformly (fun k : ℕ => fun z : ℂ =>
        aeval (z^2/(k:ℂ)^2) (nesterovAt b k))
      (fun z => jacobi.Bessel.normalized ((b/2:ℝ):ℂ) (z^2)) atTop := by
  -- Both parity estimates hold on the same joint filter before the actual parity is selected.
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro z
  have hm : Tendsto (fun p : ℕ × ℂ => ((p.1-1)/2,p.2))
      (atTop×ˢ𝓝 z) (atTop×ˢ𝓝 z) :=
    (nesterov_degree_tendsto.comp tendsto_fst).prodMk tendsto_snd
  have hp (e : ℕ) : Tendsto (fun p : ℕ × ℂ =>
      aeval (p.2^2/((2*((p.1-1)/2)+1+e:ℕ):ℂ)^2)
        (nesterovResidual b ((p.1-1)/2) e)) (atTop×ˢ𝓝 z)
        (𝓝 (jacobi.Bessel.normalized ((b/2:ℝ):ℂ) (z^2))) := by
    have h := (nesterov_landweber_joint_limit e z).mul (nesterov_factor_joint_limit hb e z)
    simpa only [Function.comp_def,nesterovResidual,map_mul,map_pow,map_sub,map_one,aeval_X,
      one_mul] using h.comp hm
  have h := tendsto_parity_choice (fun e (p : ℕ × ℂ) =>
    aeval (p.2^2/((2*((p.1-1)/2)+1+e:ℕ):ℂ)^2) (nesterovResidual b ((p.1-1)/2) e))
    (fun p : ℕ × ℂ => (p.1-1)%2)
    (fun p => by omega) (hp 0) (hp 1)
  have hr : Tendsto (fun p : ℕ × ℂ => aeval (p.2^2/(p.1:ℂ)^2) (nesterovAt b p.1))
      (atTop×ˢ𝓝 z) (𝓝 (jacobi.Bessel.normalized ((b/2:ℝ):ℂ) (z^2))) := by
    apply h.congr'
    filter_upwards [tendsto_fst.eventually (eventually_gt_atTop (0:ℕ))] with p hp
    rw [nesterov_index hp]
    rfl
  have hg := (jacobi.Bessel.normalized_analytic ((b/2:ℝ):ℂ) (z^2)).continuousAt.tendsto.comp
    ((tendsto_snd : Tendsto (fun p : ℕ × ℂ => p.2) (atTop×ˢ𝓝 z) (𝓝 z)).pow 2)
  exact (hg.prodMk hr).mono_right (by rw [← nhds_prod_eq]; exact nhds_le_uniformity _)

/-- The source Nesterov hard-edge limit holds uniformly on every compact complex set for the complete iteration sequence.
Use: provides the exact printed compact-uniform conclusion independently of any parity restriction.
Article: jacobi, Proposition A.1.
Proof: restrict the complete locally uniform limit to the compact set. -/
theorem nesterov_all_hard_edge_uniform {b : ℝ} (hb : -1<b)
    {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun k : ℕ => fun z : ℂ =>
        aeval (z^2/(k:ℂ)^2) (nesterovAt b k))
      (fun z => jacobi.Bessel.normalized ((b/2:ℝ):ℂ) (z^2)) atTop K := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  exact (tendstoLocallyUniformlyOn_univ.mpr (nesterov_all_hard_edge hb)).mono (subset_univ K)

/-- Every correctly numbered original Nesterov small zero has the printed Bessel squared-zero limit along the complete iteration sequence.
Use: the original lambda_(k,j) is the exhaustive increasing Jacobi ordering from nesterov_small_zero_iff, so this is the actual ordered-zero assertion of the source proposition.
Article: jacobi, Proposition A.1.
Proof: compose both proved actual parity limits with the growing Jacobi degree and merge them by the exact original parity. The limiting Bessel zero is independent of the proof of its identical parameter bound. -/
theorem nesterov_all_small_zero_limit {b : ℝ} (hb : -1<b) (j : ℕ) :
    Tendsto (fun k : ℕ => nesterovSmallZeroAt b hb ((k-1)%2) ((k-1)/2) j) atTop
      (𝓝 (jacobi.Bessel.sigma (b/2) (nesterov_parameters hb 0).1 j)) := by
  exact tendsto_parity_choice (fun e k => nesterovSmallZeroAt b hb e ((k-1)/2) j)
    (fun k => (k-1)%2) (fun k => by omega)
    ((nesterov_small_zero_limit hb 0 j).comp nesterov_degree_tendsto)
    ((nesterov_small_zero_limit hb 1 j).comp nesterov_degree_tendsto)

end
end jacobi.Applications
