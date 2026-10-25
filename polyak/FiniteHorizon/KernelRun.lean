import polyak.FiniteHorizon.PricesTail
import polyak.FiniteHorizon.PricesLimit

/-!
Article: Appendix C, the invariant zero-price trajectory class.
Use: actual finite-memory trajectories stay in the kernel; every finite segment
whose first full window has zero price has a continuation in that same class.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon

def ZeroPriceRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H : ℕ} (L : WindowPrice H) (r : HRun E A B β H) : Prop :=
  ∀ k,H≤k → L (runWindow r k)=0

theorem trace_runWindow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H : ℕ} (r : HRun E A B β H) (k : ℕ) (hk : H≤k) :
    traceWindow (runWindow r k)=windowTrace r.x H k :=
  trace_segmentWindow (r.segment k) k hk

theorem runWindow_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H : ℕ} (hB : B≠0) (r : HRun E A B β H) (k : ℕ) (hk : H≤k) :
    runWindow r k∈windowCone A B β H :=
  segmentWindow_mem hB (r.segment k) k hk le_rfl

theorem runWindow_shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H : ℕ} (r : HRun E A B β H) (l k : ℕ) (hk : H≤k) :
    runWindow (r.shift l) k=runWindow r (l+k) := by
  apply Prod.ext
  · ext i j
    change inner ℝ (r.x (l+(k-H+i))) (r.x (l+(k-H+j)))=
      inner ℝ (r.x (l+k-H+i)) (r.x (l+k-H+j))
    have hi : l+(k-H+i.val)=l+k-H+i.val:=by omega
    have hj : l+(k-H+j.val)=l+k-H+j.val:=by omega
    rw [hi,hj]
  · ext i
    change r.value (l+(k-H+(i+1)))=r.value (l+k-H+(i+1))
    congr 1
    omega

theorem ZeroPriceRun.shift {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β : ℝ} {H : ℕ} {L : WindowPrice H} {r : HRun E A B β H}
    (hr : ZeroPriceRun L r) (l : ℕ) : ZeroPriceRun L (r.shift l) := by
  intro k hk
  rw [runWindow_shift r l k hk]
  exact hr (l+k) (by omega)

theorem zeroPriceRun_of_initial {A B β T : ℝ} {H d : ℕ}
    (hB : B≠0) (L : WindowPrice H) (hpos : PriceNonnegative A B β H L)
    (hstep : PriceContracts A B β H T L)
    (r : HRun (EuclideanSpace ℝ (Fin d)) A B β H) (hzero : L (runWindow r H)=0) :
    ZeroPriceRun L r := by
  have hnext (k : ℕ) (hk : H≤k) (hz : L (runWindow r k)=0) :
      L (runWindow r (k+1))=0 := by
    have hrel : (runWindow r k,runWindow r (k+1))∈windowTransitions A B β H :=
      ⟨d,k+1,r.segment (k+1),k,hk,le_rfl,rfl,rfl⟩
    exact (priceKernel_forward hB L hpos hstep ⟨runWindow_mem hB r k hk,hz⟩ hrel).2
  intro k hk
  obtain ⟨l,rfl⟩:=Nat.exists_eq_add_of_le hk
  induction l with
  | zero => simpa only [Nat.add_zero] using hzero
  | succ l ih => simpa only [Nat.add_succ] using hnext (H+l) (by omega) (ih (by omega))

theorem runWindow_eq_segmentWindow {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {A B β : ℝ} {H n : ℕ}
    (s : HSegment E A B β H n) (r : HRun E A B β H)
    (hx : ∀ i,i≤n+1 → r.x i=s.x i)
    (hv : ∀ i,1 ≤ i → i≤n → r.σ i=s.σ i ∧ r.value i=s.value i)
    (k : ℕ) (hk : H≤k) (hkn : k≤n) : runWindow r k=segmentWindow s k := by
  apply Prod.ext
  · ext i j
    change inner ℝ (r.x (k-H+i)) (r.x (k-H+j))=
      inner ℝ (s.x (k-H+i)) (s.x (k-H+j))
    rw [hx _ (by omega),hx _ (by omega)]
  · ext i
    exact (hv (k-H+(i+1)) (by omega) (by omega)).2

theorem exists_zeroPriceRun {A B β T : ℝ} {H n d : ℕ}
    (hB : B≠0) (L : WindowPrice H) (hpos : PriceNonnegative A B β H L)
    (hstep : PriceContracts A B β H T L)
    (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n) (hH : H≤n)
    (hzero : L (segmentWindow s H)=0) :
    ∃ r : HRun (EuclideanSpace ℝ (Fin d)) A B β H,ZeroPriceRun L r ∧
      (∀ i,i≤n+1 → r.x i=s.x i) ∧
      ∀ k,H≤k → k≤n → runWindow r k=segmentWindow s k := by
  obtain ⟨r,hx,hv⟩:=s.exists_hRun
  have he:=runWindow_eq_segmentWindow s r hx hv
  refine ⟨r,zeroPriceRun_of_initial hB L hpos hstep r ?_,hx,he⟩
  rw [he H le_rfl hH]
  exact hzero

end polyak.FiniteHorizon
