import krylov.Convergence.SlidingRFCOldest

/-!
Article: main_krylov, thm:Ip, genuine RFC window ages.
Use: retain a uniform linear budget in the second-oldest error for every
newer stored endpoint and the true bounded current probe. Source: actual
superlinear error monotonicity and chronological current-probe arrays.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Methods
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] {n : ℕ}

/-- Real chronological anchors with the actual current probe anchor last. -/
def rfcFrameAnchor (x : ℕ → E) (k : ℕ) : Fin (n+2) → E :=
  Fin.snoc (fun i : Fin (n+1)=>x (k+i.val)) (x (k+n+1))

/-- Real chronological endpoints with the actual evaluated probe last. -/
def rfcFrameEndpoint (x v : ℕ → E) (k : ℕ) : Fin (n+2) → E :=
  Fin.snoc (fun i : Fin (n+1)=>x (k+i.val+1)) (x (k+n+1)+v k)

/-- The augmented arrays contain exactly the old accepted steps and the
actual evaluated current displacement. -/
theorem rfcFrame_steps (x v : ℕ → E) (k : ℕ) :
    (fun i=>rfcFrameEndpoint (n:=n) x v k i-rfcFrameAnchor x k i)=
      Fin.snoc (windowStep (n:=n+1) x k) (v k) := by
  funext i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [rfcFrameAnchor,rfcFrameEndpoint,Fin.snoc_last,add_sub_cancel_left]
  · simp only [rfcFrameAnchor,rfcFrameEndpoint,Fin.snoc_castSucc,windowStep]

theorem rfcFrame_images (G : E → E) (x v : ℕ → E) (k : ℕ) :
    (fun i=>G (rfcFrameEndpoint (n:=n) x v k i)-G (rfcFrameAnchor x k i))=
      Fin.snoc (windowImage (n:=n+1) G x k) (G (x (k+n+1)+v k)-G (x (k+n+1))) := by
  funext i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [rfcFrameAnchor,rfcFrameEndpoint,Fin.snoc_last]
  · simp only [rfcFrameAnchor,rfcFrameEndpoint,Fin.snoc_castSucc,windowImage]

omit [NormedAddCommGroup E] in
theorem rfcFrame_anchor_zero (x : ℕ → E) (k : ℕ) : rfcFrameAnchor (n:=n) x k 0=x k := by
  change rfcFrameAnchor (n:=n) x k (Fin.castSucc (0:Fin (n+1)))=x k
  simp only [rfcFrameAnchor,Fin.snoc_castSucc,Fin.val_zero,Nat.add_zero]

theorem rfcFrame_endpoint_zero (x v : ℕ → E) (k : ℕ) : rfcFrameEndpoint (n:=n) x v k 0=x (k+1) := by
  change rfcFrameEndpoint (n:=n) x v k (Fin.castSucc (0:Fin (n+1)))=x (k+1)
  simp only [rfcFrameEndpoint,Fin.snoc_castSucc,Fin.val_zero,Nat.add_zero]

/-- The actual augmented newer radius has a linear second-oldest budget,
including the true bounded probe. No source-envelope premise is supplied. -/
theorem superlinear_rfc_newer_radius (x v : ℕ → E)
    (hs : (fun k=>x (k+1))=o[atTop](fun k=>‖x k‖))
    {cP : ℝ} (hp : ∀ᶠ k in atTop,‖v k‖≤cP*‖x (k+n+1)‖) :
    ∀ᶠ k in atTop,newerWindowRadius (rfcFrameAnchor (n:=n) x k) (rfcFrameEndpoint x v k)≤
      (2*((n+1:ℕ):ℝ)*(1+|cP|))*‖x (k+1)‖ := by
  have hmono : ∀ᶠ k in atTop,‖x (k+1)‖≤‖x k‖ := by
    simpa only [norm_norm,one_mul] using hs.def (by norm_num : (0:ℝ)<1)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hmono
  have htail (o j : ℕ) (ho : N≤o) : ‖x (o+j)‖≤‖x o‖ := by
    induction j with
    | zero => simp only [Nat.add_zero];exact le_rfl
    | succ j ih => exact (hN (o+j) (by omega)).trans ih
  filter_upwards [hp,eventually_ge_atTop N] with k hk hNk
  let R := 1+|cP|
  have hR : 1≤R := by dsimp only [R];linarith [abs_nonneg cP]
  have hc : ‖x (k+n+1)‖≤‖x (k+1)‖ := by
    simpa only [show k+1+n=k+n+1 by omega] using htail (k+1) n (by omega)
  have hpair (i : Fin (n+2)) : i≠0 →
      ‖rfcFrameAnchor x k i‖+‖rfcFrameEndpoint x v k i‖≤2*R*‖x (k+1)‖ := by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · intro _
      simp only [rfcFrameAnchor,rfcFrameEndpoint,Fin.snoc_last]
      have hv := hk.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
      have hsum := (norm_add_le (x (k+n+1)) (v k)).trans (add_le_add le_rfl hv)
      have hcs := mul_le_mul_of_nonneg_left hc (show 0≤2+|cP| by positivity)
      have hRs : (2+|cP|)*‖x (k+1)‖≤2*R*‖x (k+1)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp only [R]
        linarith [abs_nonneg cP]
      exact (by nlinarith only [hsum,hcs] : ‖x (k+n+1)‖+‖x (k+n+1)+v k‖≤(2+|cP|)*‖x (k+1)‖).trans hRs
    · intro hi
      have hj : 0<j.val := by
        by_contra! hz
        apply hi
        exact Fin.ext (by simp only [Fin.val_castSucc,Fin.val_zero];omega)
      have h₁ := htail (k+1) (j.val-1) (by omega)
      have h₂ := htail (k+1) j.val (by omega)
      simp only [show k+1+(j.val-1)=k+j.val by omega,show k+1+j.val=k+j.val+1 by omega] at h₁ h₂
      simp only [rfcFrameAnchor,rfcFrameEndpoint,Fin.snoc_castSucc]
      have hh := add_le_add h₁ h₂
      have he := mul_le_mul_of_nonneg_right hR (show 0≤2*‖x (k+1)‖ by positivity)
      nlinarith only [hh,he]
  have hh := Finset.sum_le_sum (fun i (_hi : i∈Finset.univ)=>hpair i.succ (Fin.succ_ne_zero i))
  simpa only [newerWindowRadius,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,R,mul_assoc,mul_comm,mul_left_comm]
    using hh

end
end krylov.Convergence
