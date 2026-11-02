import krylov.Convergence.SS1FSuperlinear
import krylov.Convergence.SS1FImprovedWindow
import krylov.Convergence.SS1FQueryBound
import krylov.Convergence.RecurrenceCorrected

/-!
Article: main_krylov, thm:ss1F, improved R-order on the actual execution.
Use: derive the genuine newer-plus-oldest-squared error recurrence, then
apply the proved characteristic-order theorem. The recursion is a result
of actual value-model estimates and not a source assumption.
Source: the actual corrected diagonals, newer-column observations, (S),
and Ortega--Rheinboldt characteristic supersolutions.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Functions krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- The genuine recursive SS1-F method has the improved delayed recurrence
and the printed R-order τ₁(dimension), including dimension one and exact
zero errors. Every matrix, inverse domain and error budget is derived from
the actual function source and its observed split policy. -/
theorem ss1FSequence_improved_rorder
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (T : EuclideanSpace ℝ (Fin (n+1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0) {L₂ L₃ : ℝ≥0}
    (hH : LipschitzOnWith L₂ H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hLip : ∀ z∈S,∀ w∈S,∀ h,‖h‖=1 →
      |(T z).form h h h-(T w).form h h h|≤(L₃:ℝ)*‖z-w‖)
    {B₀ : ℝ} (hB₀ : 0≤B₀) (hT₀ : ∀ h,‖h‖=1 → |(T 0).form h h h|≤B₀)
    (split : (Fin (n+2) → EuclideanSpace ℝ (Fin (n+1))) → Fin (n+1) → ℝ)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1FSequence f G split seed) atTop (𝓝 0))
    {Cw σ : ℝ} (hCw : 0≤Cw) (hσ : 0<σ)
    (hw : ∀ᶠ k in atTop,∀ i : Fin (n+1),
      ‖splitRemainder (ss1FSequence f G split seed (k+i.val))
        (windowStep (ss1FSequence f G split seed) k i)
        (ss1FSequence f G split seed (k+n+1))
        (split (fun j=>ss1FSequence f G split seed (k+j.val)) i)‖≤
      Cw*‖ss1FSequence f G split seed (k+n+1)-ss1FSequence f G split seed (k+i.val+1)‖)
    (hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1FSequence f G split seed) k)))) :
    (∃ K : ℝ,0<K ∧∀ᶠ k in atTop,
      ‖ss1FSequence f G split seed (k+1)‖≤K*‖ss1FSequence f G split seed k‖*
        (‖ss1FSequence f G split seed (k-n)‖+‖ss1FSequence f G split seed (k-(n+1))‖^2)) ∧
    HasROrder (fun k=>‖ss1FSequence f G split seed k‖) (oneGradientRoot (n+1)) := by
  let x := ss1FSequence f G split seed
  let C := σ⁻¹
  let B := B₀+(L₃:ℝ)
  let D₁ := (L₂:ℝ)+2*B*Cw+(L₃:ℝ)*(4+2*Cw)
  let D₂ := (L₃:ℝ)/3
  let ε := fun k=>((n+1:ℕ):ℝ)*improvedValueWindowBudget L₂ L₃ B Cw ‖x k‖ ‖x (k+1)‖
  have hC : 0≤C := inv_nonneg.mpr hσ.le
  have hB : 0≤B := add_nonneg hB₀ L₃.coe_nonneg
  have hD₁ : 0≤D₁ := by dsimp only [D₁]; positivity
  have hD₂ : 0≤D₂ := by dsimp only [D₂]; positivity
  have hsuper := ss1FSequence_superlinear f G H T S hS h₀ hnbhd hH hH₀ hf hG hG₀ hT hLip
    hB₀ hT₀ split seed hconv hCw hσ hw hind
  have hmono : ∀ᶠ k in atTop,‖x (k+1)‖≤‖x k‖ := by
    simpa only [one_mul,norm_norm] using hsuper.def (by norm_num : (0:ℝ)<1)
  have hmem : ∀ᶠ k in atTop,x k∈S := hconv.eventually hnbhd
  have hunit : ∀ᶠ k in atTop,‖x k‖≤1 := by
    have hn : Tendsto (fun k=>‖x k‖) atTop (𝓝 0) := by simpa only [norm_zero] using hconv.norm
    exact (hn.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono fun _ h=>h.le
  have hε : Tendsto ε atTop (𝓝 0) := by
    have hn : Tendsto (fun k=>‖x k‖) atTop (𝓝 0) := by simpa only [norm_zero] using hconv.norm
    have hn₁ : Tendsto (fun k=>‖x (k+1)‖) atTop (𝓝 0) := hn.comp (tendsto_add_atTop_nat 1)
    have hh := ((hn₁.const_mul D₁).add ((hn.pow 2).const_mul D₂)).const_mul ((n+1:ℕ):ℝ)
    simpa only [ε,improvedValueWindowBudget,D₁,D₂,mul_zero,zero_pow (by decide : 2≠0),add_zero] using hh
  have hsmall : ∀ᶠ k in atTop,C^2*ε k≤1/2 := by
    have ht : Tendsto (fun k=>C^2*ε k) atTop (𝓝 0) := by simpa only [mul_zero] using hε.const_mul (C^2)
    exact (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))).mono fun _ h=>h.le
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hmono.and (hmem.and (hunit.and (hind.and (hw.and hsmall)))))
  have htail (o : ℕ) (ho : N≤o) (j : ℕ) : ‖x (o+j)‖≤‖x o‖ := by
    induction j with
    | zero => simp only [Nat.add_zero]; exact le_rfl
    | succ j ih => exact ((hN (o+j) (by omega)).1).trans ih
  let K := 2*C^2*((n+1:ℕ):ℝ)*(D₁+D₂)+(L₂:ℝ)+1
  have hK : 0<K := by dsimp only [K]; positivity
  have hforward (o : ℕ) (ho : N≤o) :
      ‖x (o+n+2)‖≤K*‖x (o+n+1)‖*(‖x (o+1)‖+‖x o‖^2) := by
    let a := fun i : Fin (n+1)=>x (o+i.val)
    let s := windowStep (n:=n+1) x o
    let l := split (fun i=>x (o+i.val))
    have hV := (hN o ho).2.2.2.1
    have hwo := (hN o ho).2.2.2.2.1
    have hs (i : Fin (n+1)) : s i≠0 := by
      intro hz
      have hh := windowMatrix_step_ne_zero (unitWindow s) hV.1 i
      apply hh
      simp only [unitWindow,krylov.Methods.rescaleWindow,hz,smul_zero]
    have hm (j : ℕ) : x (o+j)∈S := (hN (o+j) (by omega)).2.1
    have ha (i : Fin (n+1)) : ‖a i‖≤‖x o‖ := htail o ho i.val
    have hb (i : Fin (n+1)) : ‖a i+s i‖≤‖x (o+1)‖ := by
      simpa only [a,s,windowStep,add_sub_cancel,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
        using htail (o+1) (by omega) i.val
    have hnew (i : Fin (n+1)) (hi : i≠0) : ‖a i‖≤‖x (o+1)‖ := by
      have hip : 0 < i.val := Nat.pos_of_ne_zero (fun hz=>hi (Fin.ext hz))
      convert htail (o+1) (by omega) (i.val-1) using 1
      dsimp only [a]
      congr 2
      omega
    have hx : ‖x (o+n+1)‖≤‖x (o+1)‖ := by
      simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using htail (o+1) (by omega) n
    have hbudget (i : Fin (n+1)) (v : EuclideanSpace ℝ (Fin (n+1))) (hv : ‖v‖=1) :
        |(T (a i+s i)).form v v v|≤B := by
      have hbmem : a i+s i∈S := by simpa only [a,s,windowStep,add_sub_cancel,Nat.add_assoc] using hm (i.val+1)
      have hd := hLip (a i+s i) hbmem 0 h₀ v hv
      have hh := abs_add_le ((T (a i+s i)).form v v v-(T 0).form v v v) ((T 0).form v v v)
      simp only [sub_add_cancel] at hh
      apply hh.trans
      have hn : ‖a i+s i‖≤1 := (hb i).trans (((hN o ho).1).trans ((hN o ho).2.2.1))
      have hl : (L₃:ℝ)*‖a i+s i-0‖≤(L₃:ℝ) := by
        simpa only [sub_zero,mul_one] using mul_le_mul_of_nonneg_left hn L₃.coe_nonneg
      exact (add_le_add (hd.trans hl) (hT₀ v hv)).trans_eq (add_comm _ _)
    have hdata : ‖ss1FNormalizedError f G a s l‖≤ε o :=
      ss1F_source_improved_error_bound f G H T S hS h₀ hH hH₀ hf hG hT hLip a s l (x (o+n+1))
        (fun i=>hm i.val) (fun i=>by simpa only [a,s,windowStep,add_sub_cancel,Nat.add_assoc] using hm (i.val+1))
        (by simpa only [Nat.add_assoc] using hm (n+1)) (norm_nonneg _) (hN o ho).1 ((hN o ho).2.2.1)
        hCw hB ha hnew hb hx hs hbudget (by simpa only [a,s,l,windowStep,add_sub_cancel] using hwo)
    have hgrad := radial_gradient_endpoint_bound G H S hS h₀ hH hG hG₀ (x (o+n+1))
      (by simpa only [Nat.add_assoc] using hm (n+1))
    rw [hH₀,ContinuousLinearMap.id_apply,pow_two] at hgrad
    have hpoint := (ss1F_normalized_query_bound f G a s l (x (o+n+1)) hs hV.1
      (γ:=(L₂:ℝ)/2*‖x (o+n+1)‖) hC
      (Secant.inverse_bound_of_leastGain _ hV.1 hσ hV.2) hdata ((hN o ho).2.2.2.2.2)
      (by simpa only [mul_assoc] using hgrad)).2
    rw [show ss1FPoint f G a s l (x (o+n+1))=x (o+n+2) from (ss1FSequence_step f G split seed o).symm] at hpoint
    apply hpoint.trans
    have hrad := mul_le_mul_of_nonneg_left hx (show 0≤(L₂:ℝ)/2 by positivity)
    have h₁ : 2*C^2*((n+1:ℕ):ℝ)*D₁+(L₂:ℝ)≤K := by
      dsimp only [K]
      nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg C) (Nat.cast_nonneg (n+1))) hD₂]
    have h₂ : 2*C^2*((n+1:ℕ):ℝ)*D₂≤K := by
      dsimp only [K]
      nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg C) (Nat.cast_nonneg (n+1))) hD₁,L₂.coe_nonneg]
    have hh₁ := mul_le_mul_of_nonneg_right h₁ (norm_nonneg (x (o+1)))
    have hh₂ := mul_le_mul_of_nonneg_right h₂ (sq_nonneg ‖x o‖)
    have hcoef : 2*(C^2*ε o+(L₂:ℝ)/2*‖x (o+n+1)‖)≤K*(‖x (o+1)‖+‖x o‖^2) := by
      dsimp only [ε,improvedValueWindowBudget,D₁,D₂] at hh₁ hh₂ ⊢
      nlinarith only [hh₁,hh₂,hrad]
    exact (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)).trans_eq (by ring)
  have hrec : ∃ K : ℝ,0<K ∧∀ᶠ k in atTop,
      ‖x (k+1)‖≤K*‖x k‖*(‖x (k-n)‖+‖x (k-(n+1))‖^2) := by
    refine ⟨K,hK,?_⟩
    filter_upwards [eventually_ge_atTop (N+n+1)] with k hk
    have hh := hforward (k-(n+1)) (by omega)
    simpa only [show k-(n+1)+n+2=k+1 by omega,show k-(n+1)+n+1=k by omega,
      show k-(n+1)+1=k-n by omega] using hh
  refine ⟨hrec,?_⟩
  exact rorder_corrected_recurrence (fun k=>‖x k‖) (fun _=>norm_nonneg _)
    (by simpa only [norm_zero] using hconv.norm) (n+1) (by omega)
    (by
      obtain ⟨K,hK,hrec⟩ := hrec
      refine ⟨K,hK,?_⟩
      filter_upwards [hrec,eventually_ge_atTop (n+1)] with k hk hge
      simpa only [show k-(n+1)+1=k-n by omega] using hk)

end
end krylov.Convergence
