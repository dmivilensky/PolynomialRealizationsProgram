import krylov.Convergence.SS1Rate
import krylov.Convergence.WindowSuperlinear

/-!
Article: main_krylov, thm:Ip, sharp SS1 oldest-pair asymptotics.
Use: derive the printed single-oldest-diagonal coefficient from the actual
recursive SS1 trajectory. All newer data and radial errors are proved
little-o of the actual oldest point, using the already proved superlinearity.
Source: sharp genuine secant endpoint bounds and the exact oldest-dual
distance theorem; no assumed model decomposition or error recurrence.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Secant
  krylov.Reference krylov.LinearAlgebra chebyshev1.Nonlinear
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The actual oldest normalized-step distance used by the sliding SS1
theorem, with the true newer physical span. -/
def slidingOldestDistance (x : ℕ → EuclideanSpace ℝ (Fin (n+1))) (k : ℕ) : ℝ :=
  let V := windowMatrix (unitWindow (windowStep x k))
  Metric.infDist (euclideanColumn V 0) (newerColumnSpan V:Set _)

/-- The genuine recursive SS1 trajectory has its exact oldest-distance
leading bound. The additive remainder is little-o of its actual oldest
error; in particular every newer secant has disappeared from the leading
coefficient. -/
theorem ss1Sequence_oldest_asymptotic
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0) {L : ℝ≥0}
    (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 0)) {σ : ℝ} (hσ : 0<σ)
    (hind : ∀ᶠ k in atTop,IsUnit (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k)))) :
    ∃ r : ℕ → ℝ,r =o[atTop] (fun k=>‖ss1Sequence G seed k‖) ∧∀ᶠ k in atTop,
      ‖ss1Sequence G seed (k+n+2)‖≤
        (((L:ℝ)/2*(‖ss1Sequence G seed k‖+‖ss1Sequence G seed (k+1)‖)) /
          (slidingOldestDistance (ss1Sequence G seed) k)^2+r k)*
        ‖ss1Sequence G seed (k+n+1)‖ := by
  let x := ss1Sequence G seed
  let a := fun k (i : Fin (n+1))=>x (k+i.val)
  let b := fun k (i : Fin (n+1))=>x (k+i.val+1)
  let V := fun k=>windowMatrix (unitWindow (windowStep x k))
  let X := fun k=>windowDataError (unitWindow (windowStep (n:=n+1) x k))
    (unitWindowImages (windowStep x k) (windowImage G x k))
  let A := fun k=>secantMatrix (averagedDerivative H 0 (x (k+n+1)))
  let q := fun k=>‖x k‖
  have hsuper := ss1Sequence_superlinear G H S hS h₀ hnbhd hH hH₀ hG hG₀ seed hconv hσ hind
  have ha (i : Fin (n+1)) : Tendsto (fun k=>a k i) atTop (𝓝 0) :=
    hconv.comp (tendsto_add_atTop_nat i.val)
  have hb (i : Fin (n+1)) : Tendsto (fun k=>b k i) atTop (𝓝 0) := by
    simpa only [b,x,Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
  have hx : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
    simpa only [x,Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (n+1))
  have hm : ∀ᶠ k in atTop,(∀ i,a k i∈S) ∧(∀ i,b k i∈S) ∧x (k+n+1)∈S :=
    ((Filter.eventually_all.mpr fun i=>(ha i).eventually hnbhd).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hnbhd)).and
      (hx.eventually hnbhd) |>.mono fun _ h=>⟨h.1.1,h.1.2,h.2⟩
  have hs : ∀ᶠ k in atTop,∀ i,windowStep (n:=n+1) x k i≠0 := by
    filter_upwards [hind] with k hk i
    intro hz
    have hh := windowMatrix_step_ne_zero (unitWindow (windowStep x k)) hk.1 i
    apply hh
    simp only [unitWindow,rescaleWindow,hz,smul_zero]
  have hV : ∀ᶠ k in atTop,‖(V k)⁻¹‖≤σ⁻¹ :=
    hind.mono fun _ h=>inverse_bound_of_leastGain _ h.1 hσ h.2
  have hdiagBound : ∀ᶠ k in atTop,|X k 0 0|≤(L:ℝ)/2*(q k+‖x (k+1)‖) := by
    filter_upwards [hm,hs] with k hk hsk
    have hstep : (fun i : Fin (n+1)=>b k i-a k i)=windowStep x k := rfl
    have himage : (fun i : Fin (n+1)=>G (b k i)-G (a k i))=windowImage G x k := rfl
    have hh := source_window_entry_bound G H S hS h₀ hH hH₀ hG (a k) (b k) hk.1 hk.2.1 hsk 0 0
    rw [hstep,himage] at hh
    simpa only [X,a,b,q,Fin.val_zero,Nat.add_zero,max_self] using hh
  have hnext := superlinear_window_tail x hsuper 0
  have hcurrent := superlinear_window_tail x hsuper n
  have hdiag : (fun k=>X k 0 0) =O[atTop] q := by
    apply IsBigO.of_bound (L:ℝ)
    filter_upwards [hdiagBound,hnext.def (by norm_num : (0:ℝ)<1)] with k hk hnk
    simp only [norm_norm,one_mul] at hnk
    simpa only [Real.norm_eq_abs,abs_norm,q] using hk.trans (by nlinarith [L.coe_nonneg])
  have hrest : (fun k=>X k-X k 0 0 • vecMulVec (Pi.single 0 1) (Pi.single 0 1)) =o[atTop] q := by
    have hbnd : (fun k=>X k-X k 0 0 • vecMulVec (Pi.single 0 1) (Pi.single 0 1)) =O[atTop]
        (fun k=>newerWindowRadius (a k) (b k)) := by
      apply IsBigO.of_bound (((n+1:ℕ):ℝ)*((L:ℝ)/2))
      filter_upwards [hm,hs] with k hk hsk
      have hh := source_window_newer_bound G H S hS h₀ hH hH₀ hG (a k) (b k) hk.1 hk.2.1 hsk
      have hstep : (fun i : Fin (n+1)=>b k i-a k i)=windowStep x k := rfl
      have himage : (fun i : Fin (n+1)=>G (b k i)-G (a k i))=windowImage G x k := rfl
      dsimp only at hh
      rw [hstep,himage] at hh
      simpa only [X,Real.norm_of_nonneg (newerWindowRadius_nonneg _ _),mul_assoc] using hh
    exact hbnd.trans_isLittleO (superlinear_newer_window_radius x hsuper)
  have hnew : (fun k=>A k-1) =o[atTop] q := by
    have hbnd : (fun k=>A k-1) =O[atTop] (fun k=>‖x (k+n+1)‖) := by
      apply IsBigO.of_bound ((L:ℝ)/2)
      filter_upwards [hm] with k hk
      rw [show ‖A k-1‖=‖averagedDerivative H 0 (x (k+n+1))-ContinuousLinearMap.id ℝ _‖ from
        secantMatrix_sub_one _]
      have hh := secant_operator_endpoint_bound H S hS h₀ hH 0 (x (k+n+1)) h₀ hk.2.2
      simpa only [hH₀,norm_zero,zero_add,sub_zero,norm_norm] using hh
    exact hbnd.trans_isLittleO hcurrent
  have hA : Tendsto A atTop (𝓝 1) := tendsto_iff_norm_sub_tendsto_zero.mpr
    (hnew.norm_left.trans_tendsto (by simpa only [q,norm_zero] using hconv.norm))
  have hX : Tendsto X atTop (𝓝 0) := by
    let ε := fun k=>(L:ℝ)/2*sourceWindowRadius (a k) (b k)
    have hε : Tendsto ε atTop (𝓝 0) := by
      have hh := tendsto_finsetSum Finset.univ (fun i _=>(ha i).norm.add (hb i).norm)
      have hr : Tendsto (fun k=>sourceWindowRadius (a k) (b k)) atTop (𝓝 0) := by
        simpa only [sourceWindowRadius,norm_zero,add_zero,Finset.sum_const_zero] using hh
      simpa only [mul_zero] using hr.const_mul ((L:ℝ)/2)
    apply squeeze_zero_norm' (a:=fun k=>((n+1:ℕ):ℝ)*ε k)
    · filter_upwards [hm,hs] with k hk hsk
      exact windowDataError_norm _ _ (unitWindow_norm _ hsk)
        (mul_nonneg (by positivity) (sourceWindowRadius_nonneg _ _))
        (source_unit_window_error G H S hS h₀ hH hH₀ hG _ _ hk.1 hk.2.1 hsk)
    · simpa only [mul_zero] using hε.const_mul ((n+1:ℕ):ℝ)
  obtain ⟨r,hr,hbound⟩ := oldest_model_asymptotic_bound V X A (fun k=>x (k+n+1)) q
    (inv_nonneg.mpr hσ.le) (hind.mono fun _ h=>h.1) hV hX hA hdiag hrest hnew
  refine ⟨r,hr,?_⟩
  filter_upwards [hbound,hm,hs,hind,hdiagBound] with k hk hmk hsk hvk hd
  have hrad : cgOperator (A k) (x (k+n+1))=G (x (k+n+1)) := by
    rw [secantMatrix_operator]
    have hp t (ht : t∈Icc (0:ℝ) 1) : (0:EuclideanSpace ℝ (Fin (n+1)))+t • x (k+n+1)∈S :=
      hS.add_smul_mem h₀ (by simpa only [zero_add] using hmk.2.2) ht
    have hc := hH.continuousOn.comp
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
    simpa only [zero_add,hG₀,sub_zero] using
      averagedDerivative_apply G H 0 (x (k+n+1)) hc (fun t ht=>hG _ (hp t ht))
  have hmodel := window_model_error (unitWindow (windowStep (n:=n+1) x k))
    (unitWindowImages (windowStep x k) (windowImage G x k)) hvk.1
  have hj : inverseCongruence (V k)
      (ss1Model (unitWindow (windowStep x k)) (unitWindowImages (windowStep x k) (windowImage G x k)))=
      1+inverseCongruence (V k) (X k) := by rw [←hmodel]; abel
  have hquery : x (k+n+2)=x (k+n+1)-
      cgOperator (1+inverseCongruence (V k) (X k))⁻¹ (G (x (k+n+1))) := by
    rw [show x (k+n+2)=ss1Point (windowStep (n:=n+1) x k) (windowImage G x k)
      (G (x (k+n+1))) (x (k+n+1)) from ss1Sequence_step G seed k]
    rw [←ss1Point_rescale _ _ _ (unitWindow_diagonal_unit _ hsk)]
    change ss1Point (unitWindow (windowStep x k))
      (unitWindowImages (windowStep x k) (windowImage G x k)) (G (x (k+n+1))) (x (k+n+1))=_
    rw [ss1Point_eq_model_step _ _ _ _ hvk.1,hj]
  have heq : WithLp.toLp 2 (WithLp.ofLp (x (k+n+1))-
      (1+inverseCongruence (V k) (X k))⁻¹*ᵥ(A k*ᵥWithLp.ofLp (x (k+n+1))))=x (k+n+2) := by
    rw [hquery,←hrad]
    rfl
  rw [heq] at hk
  exact hk.trans (mul_le_mul_of_nonneg_right
    (add_le_add (div_le_div_of_nonneg_right hd (sq_nonneg _)) le_rfl) (norm_nonneg _))

end
end krylov.Convergence
