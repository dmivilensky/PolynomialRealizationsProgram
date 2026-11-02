import krylov.Convergence.SlidingFCPath

/-!
Article: main_krylov, thm:G, invariant observed-path rate estimates.
Use: prove the source inequalities from true searches and exact observed
triangular conjugacy. Metric wrappers derive these execution identities
from the physical observed inverse; no rate or conditioning is presumed.
Source: the same source staircase and radial Taylor proofs as thm:G.
-/

/-!
Article: krylov, Proposition E.18 [thm:G].

The physical sliding executor supplies automatic asymptotic orthogonality/conditioning; the
exact delayed product, R-order and conditional sharp half coefficient follow.
Canonical centering changes only coordinates, not the observed direction. The half coefficient
retains the additional Q-superlinearity assumption; no independent-window condition is added.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods krylov.Functions
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
set_option maxHeartbeats 1200000

/-- The actual sliding FC executor satisfies the printed delayed product,
with a factor arbitrarily close to one and the exact leading constant.
Only convergence and defined actual observed solves supplement the local
source assumptions. -/
theorem source_path_product_bound
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,
      HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z)
    (x d : ℕ → EuclideanSpace ℝ (Fin (n+2))) (hconv : Tendsto x atTop (𝓝 0))
    (hsteps : ∀ᶠ k in atTop,∀ i : Fin (n+2),windowStep (n:=n+2) x k i≠0)
    (hconj : ∀ᶠ k in atTop,∀ i j : Fin (n+2),i<j →
      inner ℝ (windowImage G x k i) (windowStep x k j)=0)
    (hsearch : ∀ᶠ k in atTop,IsChordMinimum f (x k) (d k) r (x (k+1)))
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ k in atTop,‖x (k+n+2)‖≤
      (4*(L:ℝ)*((n+1:ℕ):ℝ)*Real.sqrt (n+1)*(1+δ)^4)*
        ‖x k‖*‖x (k+1)‖ := by
  let θ := 1+δ
  have hθ : 0<θ := by dsimp only [θ]; linarith
  let V := fun k=>windowMatrix (unitWindow (windowStep (n:=n+2) x k))
  have hframe := source_path_frame_conditioning G H hr hH₀ hH hG x hconv hsteps hconj
  have hunit : ∀ᶠ k in atTop,IsUnit (V k).det := hframe.2.1
  have hinv : ∀ᶠ k in atTop,‖(V k)⁻¹‖≤θ :=
    (hframe.2.2.eventually (gt_mem_nhds (by dsimp only [θ]; linarith : (1:ℝ)<θ))).mono fun _ h=>h.le
  have hline := (source_path_chord_control f G H hr hG₀ hH₀ hLr hH hf hG x d hconv hsearch).1
  have hnear := source_path_near_monotone f G H hr hG₀ hH₀ hLr hH hf hG
    x d hconv hsearch (n+2) hδ
  have hnear' : ∀ᶠ k in atTop,∀ j≤n+2,‖x (k+1+j)‖≤θ*‖x (k+1)‖ :=
    (tendsto_add_atTop_nat 1).eventually hnear
  have hmem : ∀ᶠ k in atTop,‖x k‖<r := by
    have hh : Tendsto (fun k=>‖x k‖) atTop (𝓝 0) := by simpa only [norm_zero] using hconv.norm
    exact hh.eventually (gt_mem_nhds hr)
  have hsmall : ∀ᶠ k in atTop,θ*((L:ℝ)/2*‖x k‖)≤δ := by
    have hh : Tendsto (fun k=>θ*((L:ℝ)/2*‖x k‖)) atTop (𝓝 0) := by
      simpa only [norm_zero,mul_zero] using (hconv.norm.const_mul ((L:ℝ)/2)).const_mul θ
    exact (hh.eventually (gt_mem_nhds hδ)).mono fun _ h=>h.le
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hmem.and (hline.and hsmall))
  filter_upwards [eventually_ge_atTop N,hunit,hinv,hconj,hnear,hnear'] with k hk hu hi hc hn hn'
  have hball j (hj : j≤n+2) : ‖x (k+j)‖≤θ*‖x k‖ := hn j hj
  have hnew j (hj₀ : 0<j) (hj : j≤n+2) : ‖x (k+j)‖≤θ*‖x (k+1)‖ := by
    have hh := hn' (j-1) (by omega)
    simpa only [show k+1+(j-1)=k+j by omega] using hh
  have hsteps : windowStep (n:=n+2) (fun j=>x (k+j)) 0=windowStep x k := by
    funext i
    simp only [windowStep,Nat.zero_add,Nat.add_assoc]
  have hsrc := source_conjugate_path_residual f G H hH hf hG (fun j=>x (k+j))
    (mul_nonneg hθ.le (norm_nonneg _)) (mul_nonneg hθ.le (norm_nonneg _))
    (fun j _=> (hN (k+j) (by omega)).1) hball hnew
    (fun j _=>by simpa only [Nat.add_assoc] using (hN (k+j) (by omega)).2.1)
    (fun i j hij hj=>by
      simpa only [windowImage,windowStep,Nat.add_assoc] using hc
        (⟨i,by omega⟩ : Fin (n+2)) (⟨j,by omega⟩ : Fin (n+2)) hij)
    (by rw [hsteps]; exact hu)
  have hgrad : ‖x (k+n+2)‖≤θ*‖G (x (k+n+2))‖ := by
    have hm : x (k+n+2)∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using (hN (k+n+2) (by omega)).1.le
    have he := radial_gradient_endpoint_bound G H (Metric.closedBall 0 r) (convex_closedBall _ _)
      (by simpa using hr.le) hH hG hG₀ (x (k+n+2)) hm
    rw [hH₀,ContinuousLinearMap.id_apply] at he
    have ht := norm_add_le (G (x (k+n+2))) (x (k+n+2)-G (x (k+n+2)))
    rw [add_sub_cancel,norm_sub_rev] at ht
    have hs := (hN (k+n+2) (by omega)).2.2
    have hmul := mul_le_mul_of_nonneg_right hs (norm_nonneg (x (k+n+2)))
    have ht' := ht.trans (add_le_add le_rfl he)
    have ht'' := mul_le_mul_of_nonneg_left ht' hθ.le
    dsimp only [θ] at hmul ht'' ⊢
    nlinarith only [hmul,ht'']
  have hsrc' : ‖G (x (k+n+2))‖≤‖(V k)⁻¹‖*
      (Real.sqrt (n+1)*(((n+1:ℕ):ℝ)*(4*(L:ℝ)*(θ*‖x k‖)*(θ*‖x (k+1)‖)))) := by
    simpa only [hsteps,←Nat.add_assoc,Nat.cast_add,Nat.cast_one] using hsrc
  have hb := hgrad.trans (mul_le_mul_of_nonneg_left hsrc' hθ.le)
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hi (by positivity : 0≤Real.sqrt (n+1)*
      (((n+1:ℕ):ℝ)*(4*(L:ℝ)*(θ*‖x k‖)*(θ*‖x (k+1)‖))))) hθ.le
  convert hh using 1
  simp only [θ,Nat.cast_add,Nat.cast_one]
  ring

/-- The original leading constant in its precise epsilon formulation of
the printed (1+o(1)) inequality. In particular this includes a zero
Lipschitz constant without division by it. -/
theorem source_path_sharp_product
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,
      HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z)
    (x d : ℕ → EuclideanSpace ℝ (Fin (n+2))) (hconv : Tendsto x atTop (𝓝 0))
    (hsteps : ∀ᶠ k in atTop,∀ i : Fin (n+2),windowStep (n:=n+2) x k i≠0)
    (hconj : ∀ᶠ k in atTop,∀ i j : Fin (n+2),i<j →
      inner ℝ (windowImage G x k i) (windowStep x k j)=0)
    (hsearch : ∀ᶠ k in atTop,IsChordMinimum f (x k) (d k) r (x (k+1)))
    {η : ℝ} (hη : 0<η) :
    ∀ᶠ k in atTop,‖x (k+n+2)‖≤
      (4*(L:ℝ)*((n+1:ℕ):ℝ)*Real.sqrt (n+1)+η)*
        ‖x k‖*‖x (k+1)‖ := by
  let C₀ := 4*(L:ℝ)*((n+1:ℕ):ℝ)*Real.sqrt (n+1)
  have hc : ContinuousAt (fun t : ℝ=>C₀*(1+t)^4) 0 := by fun_prop
  have he : ∀ᶠ t : ℝ in 𝓝 0,C₀*(1+t)^4<C₀+η := by
    have hh := hc.tendsto.eventually (gt_mem_nhds (by simp only [add_zero,one_pow,mul_one]; linarith :
      C₀*(1+(0:ℝ))^4<C₀+η))
    exact hh
  obtain ⟨ρ,hρ,hnear⟩ := Metric.eventually_nhds_iff.mp he
  have hδ : 0<ρ/2 := by linarith
  have hcoeff := hnear (y:=ρ/2) (by
    rw [Real.dist_eq,sub_zero,abs_of_pos hδ]
    linarith)
  filter_upwards [source_path_product_bound f G H hr hG₀ hH₀ hLr hH hf hG x d hconv hsteps hconj hsearch hδ]
    with k hk
  exact hk.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff.le (norm_nonneg _)) (norm_nonneg _))

/-- The actual independence-free sliding FC method has the characteristic
R-order τ_FC(dimension), per iteration and hence per gradient. -/
theorem source_path_rorder
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,
      HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z)
    (x d : ℕ → EuclideanSpace ℝ (Fin (n+2))) (hconv : Tendsto x atTop (𝓝 0))
    (hsteps : ∀ᶠ k in atTop,∀ i : Fin (n+2),windowStep (n:=n+2) x k i≠0)
    (hconj : ∀ᶠ k in atTop,∀ i j : Fin (n+2),i<j →
      inner ℝ (windowImage G x k i) (windowStep x k j)=0)
    (hsearch : ∀ᶠ k in atTop,IsChordMinimum f (x k) (d k) r (x (k+1)))
    : HasROrder (fun k=>‖x k‖) (fullConjugacyRoot (n+2)) := by
  let C₀ := 4*(L:ℝ)*((n+1:ℕ):ℝ)*Real.sqrt (n+1)
  have hC₀ : 0≤C₀ := by dsimp only [C₀]; positivity
  have hb := source_path_product_bound f G H hr hG₀ hH₀ hLr hH hf hG x d hconv hsteps hconj hsearch
    (by norm_num : (0:ℝ)<1)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  have hrec : ∃ K : ℝ,0<K ∧∀ᶠ k in atTop,
      ‖x (k+1)‖≤K*‖x (k-(n+1))‖*‖x (k-n)‖ := by
    refine ⟨C₀*16+1,by positivity,?_⟩
    filter_upwards [eventually_ge_atTop (N+n+1)] with k hk
    let o := k-(n+1)
    have ho : N≤o := by dsimp only [o]; omega
    have hh := hN o ho
    have he₀ : o+n+2=k+1 := by dsimp only [o]; omega
    have he₁ : o+1=k-n := by dsimp only [o]; omega
    have hcoef : 4*(L:ℝ)*((n+1:ℕ):ℝ)*Real.sqrt (n+1)*(1+1)^4≤C₀*16+1 := by
      dsimp only [C₀]
      norm_num
    have ht := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (norm_nonneg (x o))) (norm_nonneg (x (o+1)))
    have hh' : ‖x (k+1)‖≤(C₀*16+1)*‖x o‖*‖x (k-n)‖ := by
      simpa only [he₀,he₁] using hh.trans ht
    exact hh'
  have hh := rorder_product_recurrence (fun k=>‖x k‖) (fun _=>norm_nonneg _)
    (by simpa only [norm_zero] using hconv.norm) (n+1) n (by omega) hrec
  simpa only [fullConjugacyRoot,show n+2-1=n+1 by omega,show n+2-2=n by omega] using hh

/-- A quantitative neighbourhood of the printed half coefficient, on the
actual superlinear sliding FC trajectory. -/
theorem source_path_half_product_aux
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,
      HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z)
    (x d : ℕ → EuclideanSpace ℝ (Fin (n+2))) (hconv : Tendsto x atTop (𝓝 0))
    (hsteps : ∀ᶠ k in atTop,∀ i : Fin (n+2),windowStep (n:=n+2) x k i≠0)
    (hconj : ∀ᶠ k in atTop,∀ i j : Fin (n+2),i<j →
      inner ℝ (windowImage G x k i) (windowStep x k j)=0)
    (hsearch : ∀ᶠ k in atTop,IsChordMinimum f (x k) (d k) r (x (k+1)))
    (hs : (fun k=>x (k+1))=o[atTop]
      (fun k=>‖x k‖))
    {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ k in atTop,‖x (k+n+2)‖≤
      ((1+δ)^2*((L:ℝ)/2*(1+δ)^3+δ))*
        ‖x k‖*‖x (k+1)‖ := by
  let θ := 1+δ
  have hθ : 0<θ := by dsimp only [θ];linarith
  let V := fun k=>windowMatrix (unitWindow (windowStep (n:=n+2) x k))
  have hframe := source_path_frame_conditioning G H hr hH₀ hH hG x hconv hsteps hconj
  have hinv : ∀ᶠ k in atTop,‖(V k)⁻¹‖≤θ :=
    (hframe.2.2.eventually (gt_mem_nhds (by dsimp only [θ];linarith : (1:ℝ)<θ))).mono fun _ h=>h.le
  have hline := (source_path_chord_control f G H hr hG₀ hH₀ hLr hH hf hG x d hconv hsearch).1
  have hlines : ∀ᶠ k in atTop,∀ j : Fin (n+2),
      inner ℝ (x (k+j.val+1)-x (k+j.val)) (G (x (k+j.val+1)))=0 :=
    Filter.eventually_all.mpr fun j=>(tendsto_add_atTop_nat j.val).eventually hline
  have hmem : ∀ᶠ k in atTop,∀ j : Fin (n+3),‖x (k+j.val)‖<r := by
    apply Filter.eventually_all.mpr
    intro j
    have ht : Tendsto (fun k=>‖x (k+j.val)‖) atTop (𝓝 0) := by
      simpa only [Function.comp_def,norm_zero] using (hconv.comp (tendsto_add_atTop_nat j.val)).norm
    exact ht.eventually (gt_mem_nhds hr)
  have hsmall : ∀ᶠ k in atTop,θ*((L:ℝ)/2*‖x (k+n+2)‖)≤δ := by
    have hh : Tendsto (fun k=>θ*((L:ℝ)/2*‖x (k+n+2)‖)) atTop (𝓝 0) := by
      have ht := (hconv.comp (tendsto_add_atTop_nat (n+2))).norm
      simpa only [Function.comp_def,norm_zero,mul_zero,Nat.add_assoc] using (ht.const_mul ((L:ℝ)/2)).const_mul θ
    exact (hh.eventually (gt_mem_nhds hδ)).mono fun _ h=>h.le
  have he : ∀ᶠ k in atTop,‖x (k+1)‖≤δ*‖x k‖ := by
    simpa only [norm_norm] using hs.def hδ
  have he' := (tendsto_add_atTop_nat 1).eventually he
  have hmass := (fcPathNewerMass_littleo (n:=n) H (Metric.closedBall 0 r) (convex_closedBall _ _)
    (Metric.closedBall_mem_nhds (0:EuclideanSpace ℝ (Fin (n+2))) hr) hH x hconv hs).def hδ
  filter_upwards [hframe.2.1,hinv,hconj,hlines,hmem,hsmall,he,he',hmass]
    with k hu hi hc hl hm hsm he₀ he₁ hmass
  have hstep₀ : ‖x (k+1)-x k‖≤θ*‖x k‖ := by
    have hh := (norm_sub_le (x (k+1)) (x k)).trans (add_le_add he₀ le_rfl)
    dsimp only [θ];nlinarith only [hh]
  have hstep₁ : ‖x (k+2)-x (k+1)‖≤θ*‖x (k+1)‖ := by
    have hh := (norm_sub_le (x (k+2)) (x (k+1))).trans
      (add_le_add (by simpa only [show k+1+1=k+2 by omega] using he₁) le_rfl)
    dsimp only [θ];nlinarith only [hh]
  have hsum : ‖x (k+1)-x k‖+‖x (k+2)-x (k+1)‖≤θ^2*‖x k‖ := by
    have hb := hstep₁.trans (mul_le_mul_of_nonneg_left he₀ hθ.le)
    have hh := add_le_add hstep₀ hb
    dsimp only [θ] at hh ⊢
    nlinarith only [hh]
  have hmass' : fcPathNewerMass (n:=n) H x k≤δ*‖x k‖*‖x (k+1)‖ := by
    have hh := (le_abs_self (fcPathNewerMass (n:=n) H x k)).trans hmass
    simpa only [Real.norm_eq_abs,abs_mul,abs_norm,mul_assoc] using hh
  have hsrc := source_fc_sharp_path_residual f G H hH hf hG x k
    (fun j hj=>hm ⟨j,by omega⟩) (fun j hj=>hl ⟨j,by omega⟩)
    (fun i j hij hj=>by
      simpa only [windowImage,windowStep] using hc
        (⟨i,by omega⟩ : Fin (n+2)) (⟨j,by omega⟩ : Fin (n+2)) hij) hu
  have hlead : (L:ℝ)/2*(‖x (k+1)-x k‖+‖x (k+2)-x (k+1)‖)*‖x (k+2)-x (k+1)‖≤
      ((L:ℝ)/2*θ^3)*‖x k‖*‖x (k+1)‖ := by
    have hh := mul_le_mul
      (mul_le_mul_of_nonneg_left hsum (by positivity : 0≤(L:ℝ)/2)) hstep₁
      (norm_nonneg _) (by positivity : 0≤(L:ℝ)/2*(θ^2*‖x k‖))
    convert hh using 1; ring
  have htotal := add_le_add hlead hmass'
  have hsrc' : ‖G (x (k+n+2))‖≤θ*(((L:ℝ)/2*θ^3+δ)*‖x k‖*‖x (k+1)‖) := by
    apply hsrc.trans
    apply (mul_le_mul_of_nonneg_left htotal (norm_nonneg ((V k)⁻¹))).trans
    convert mul_le_mul_of_nonneg_right hi
      (by positivity : 0≤((L:ℝ)/2*θ^3)*‖x k‖*‖x (k+1)‖+δ*‖x k‖*‖x (k+1)‖) using 1; ring
  have hgrad : ‖x (k+n+2)‖≤θ*‖G (x (k+n+2))‖ := by
    have hxm : x (k+n+2)∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Nat.add_assoc] using (hm ⟨n+2,by omega⟩).le
    have he := radial_gradient_endpoint_bound G H (Metric.closedBall 0 r) (convex_closedBall _ _)
      (by simpa using hr.le) hH hG hG₀ (x (k+n+2)) hxm
    rw [hH₀,ContinuousLinearMap.id_apply] at he
    have ht := norm_add_le (G (x (k+n+2))) (x (k+n+2)-G (x (k+n+2)))
    rw [add_sub_cancel,norm_sub_rev] at ht
    have hmul := mul_le_mul_of_nonneg_right hsm (norm_nonneg (x (k+n+2)))
    have ht' := ht.trans (add_le_add le_rfl he)
    have ht'' := mul_le_mul_of_nonneg_left ht' hθ.le
    dsimp only [θ] at hmul ht'' ⊢
    nlinarith only [hmul,ht'']
  apply hgrad.trans
  convert mul_le_mul_of_nonneg_left hsrc' hθ.le using 1
  dsimp only [θ]
  ring

/-- The original sharpened FC constant L_H/2, in the exact epsilon
formulation of the printed limsup bound. This applies to the actual
executor, requires no independence, and includes zero error values. -/
theorem source_path_half_product
    (f : EuclideanSpace ℝ (Fin (n+2)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)))
    (H : EuclideanSpace ℝ (Fin (n+2)) → EuclideanSpace ℝ (Fin (n+2)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+2)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L:ℝ)*r≤1/2)
    (hH : LipschitzOnWith L H (Metric.closedBall 0 r))
    (hf : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,
      HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈Metric.closedBall (0:EuclideanSpace ℝ (Fin (n+2))) r,HasFDerivAt G (H z) z)
    (x d : ℕ → EuclideanSpace ℝ (Fin (n+2))) (hconv : Tendsto x atTop (𝓝 0))
    (hsteps : ∀ᶠ k in atTop,∀ i : Fin (n+2),windowStep (n:=n+2) x k i≠0)
    (hconj : ∀ᶠ k in atTop,∀ i j : Fin (n+2),i<j →
      inner ℝ (windowImage G x k i) (windowStep x k j)=0)
    (hsearch : ∀ᶠ k in atTop,IsChordMinimum f (x k) (d k) r (x (k+1)))
    (hs : (fun k=>x (k+1))=o[atTop]
      (fun k=>‖x k‖))
    {η : ℝ} (hη : 0<η) :
    ∀ᶠ k in atTop,‖x (k+n+2)‖≤
      ((L:ℝ)/2+η)*‖x k‖*‖x (k+1)‖ := by
  have hc : ContinuousAt (fun t : ℝ=>(1+t)^2*((L:ℝ)/2*(1+t)^3+t)) 0 := by fun_prop
  have he : ∀ᶠ t : ℝ in 𝓝 0,(1+t)^2*((L:ℝ)/2*(1+t)^3+t)<(L:ℝ)/2+η := by
    exact hc.tendsto.eventually (gt_mem_nhds (by simp only [add_zero,one_pow,one_mul];linarith))
  obtain ⟨ρ,hρ,hnear⟩ := Metric.eventually_nhds_iff.mp he
  have hδ : 0<ρ/2 := by linarith
  have hcoeff := hnear (y:=ρ/2) (by rw [Real.dist_eq,sub_zero,abs_of_pos hδ];linarith)
  filter_upwards [source_path_half_product_aux f G H hr hG₀ hH₀ hLr hH hf hG x d
    hconv hsteps hconj hsearch hs hδ] with k hk
  exact hk.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff.le (norm_nonneg _)) (norm_nonneg _))

end
end krylov.Convergence
