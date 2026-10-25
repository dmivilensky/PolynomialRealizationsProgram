import polyak.FiniteHorizon.StationaryKernel
import polyak.FiniteHorizon.KernelRun

/-!
Article: Appendix C, actual positivity of the constructed prices above the rate.
Use: the source banded inequality gives the exact one-step price drop; the
proved finite-memory envelope makes its terminal term vanish. Positivity on
the entire Gram cone is obtained by its actual trajectory realization.
-/
noncomputable section
namespace polyak.FiniteHorizon
universe u
open Growth Growth.FiniteHorizon Energy Interpolation Filter
open scoped BigOperators Topology

def _root_.polyak.Growth.Run.toHRun {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {A B β : ℝ}
    (r : Run E A B β) (H : ℕ) : HRun E A B β H where
  x:=r.x
  σ k:=gradient r.ψ (r.x k)
  value k:=r.ψ (r.x k)
  interpolation i _ j _ _ := (r.segment (max i j)).interpolation i (by omega) j (by omega)
  origin i _ := (r.segment i).origin i (by omega)
  recurrence:=r.recurrence

def BandedSource7 (A B β t : ℝ) (H : ℕ) (C : WindowMatrix7) (d : ℕ → ℝ) : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ∀ r : HRun E A B β H,∀ k : ℕ,H≤k →
    0≤bandedFunctional7 C d (integerDiscount (fun z => r.x z.toNat) t)
      (integerDiscountValue (fun z => sampleValue r z.toNat) t) ((k : ℤ)-6)

theorem windowPrice7_run_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β t a δ ε : ℝ} {H : ℕ} {C : WindowMatrix7} {d : ℕ → ℝ}
    (data : BandedData7 C d ε) (ha : 0<a) (hε : ε=a*δ) (hH : 7≤H)
    (r : HRun E A B β H) (k : ℕ) (hk : H≤k)
    (hsource : 0≤bandedFunctional7 C d (integerDiscount (fun z => r.x z.toNat) t)
      (integerDiscountValue (fun z => sampleValue r z.toNat) t) ((k : ℤ)-6)) :
    δ*‖r.x (k-5)‖^2≤windowPrice7 data H a t (runWindow r k)-
      Real.exp (-2*t)*windowPrice7 data H a t (runWindow r (k+1)) := by
  have hs:=windowPrice7_step data ha hε hH (fun z => r.x z.toNat)
    (fun z => sampleValue r z.toNat) (k : ℤ) hsource
  have hk1 : (k : ℤ)+1=((k+1 : ℕ) : ℤ):=by omega
  rw [integerWindow_hRun_nat r k hk,hk1,integerWindow_hRun_nat r (k+1) (by omega)] at hs
  have hkm : ((k : ℤ)-5).toNat=k-5:=by omega
  simpa only [hkm,runWindow] using hs

theorem windowPrice7_run_finite_bound {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β t a δ ε : ℝ} {H : ℕ}
    {C : WindowMatrix7} {d : ℕ → ℝ} (data : BandedData7 C d ε)
    (hB : B≠0) (ha : 0<a) (hδ : 0≤δ) (hε : ε=a*δ) (hH : 7≤H)
    (hRate : growthRate A B β H<Real.exp t) (hsource : BandedSource7.{u} A B β t H C d)
    (r : HRun E A B β H) (k : ℕ) (hk : H≤k) (N : ℕ) :
    δ*(∑ i∈Finset.range N,Real.exp (-2*t)^i*‖r.x (k+i-5)‖^2)≤
      windowPrice7 data H a t (runWindow r k) := by
  let P:=fun n => windowPrice7 data H a t (runWindow r (k+n))
  let en:=fun n => ‖r.x (k+n-5)‖^2
  have hstep : ∀ n,δ*en n≤P n-Real.exp (-2*t)*P (n+1) := by
    intro n
    have hs:=windowPrice7_run_step data ha hε hH r (k+n) (by omega) (hsource E r _ (by omega))
    simpa only [P,en,Nat.add_assoc] using hs
  have htail : Tendsto (fun n : ℕ => Real.exp (-2*t)^n*P n) atTop (𝓝 0) := by
    have ht:=discounted_window_price_tendsto_zero hB r (windowPrice7 data H a t) hRate k hk
    have hpow (n : ℕ) : Real.exp (-2*t)^n=Real.exp (-2*(n : ℝ)*t):=by
      rw [←Real.exp_nat_mul]
      congr 1
      ring
    simpa only [hpow,P] using ht
  simpa only [P,en,Nat.add_zero] using discounted_price_finite_bound P en
    (Real.exp_pos _).le hδ (fun n => sq_nonneg _) hstep htail N

theorem windowPrice7_run_nonnegative {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A B β t a δ ε : ℝ} {H : ℕ}
    {C : WindowMatrix7} {d : ℕ → ℝ} (data : BandedData7 C d ε)
    (hB : B≠0) (ha : 0<a) (hδ : 0≤δ) (hε : ε=a*δ) (hH : 7≤H)
    (hRate : growthRate A B β H<Real.exp t) (hsource : BandedSource7.{u} A B β t H C d)
    (r : HRun E A B β H) (k : ℕ) (hk : H≤k) :
    0≤windowPrice7 data H a t (runWindow r k) := by
  simpa only [Finset.range_zero,Finset.sum_empty,mul_zero] using
    windowPrice7_run_finite_bound data hB ha hδ hε hH hRate hsource r k hk 0

theorem windowPrice7_nonnegative {A B β t a δ ε : ℝ} {H : ℕ}
    {C : WindowMatrix7} {d : ℕ → ℝ} (data : BandedData7 C d ε)
    (hB : B≠0) (ha : 0<a) (hδ : 0≤δ) (hε : ε=a*δ) (hH : 7≤H)
    (hRate : growthRate A B β H<Real.exp t) (hsource : BandedSource7.{0} A B β t H C d) :
    PriceNonnegative A B β H (windowPrice7 data H a t) := by
  intro Y hY
  obtain ⟨r,hgram,hvalues⟩:=windowCone_exists_run hB hY
  have hw : runWindow (r.toHRun H) H=Y := by
    apply Prod.ext
    · change Matrix.gram ℝ (fun i : Fin (H+2) => r.x (H-H+i))=Y.1
      simpa only [Nat.sub_self,Nat.zero_add] using hgram
    · ext i
      change r.ψ (r.x (H-H+(i+1)))=Y.2 i
      simpa only [Nat.sub_self,Nat.zero_add] using hvalues i
  rw [←hw]
  exact windowPrice7_run_nonnegative data hB ha hδ hε hH hRate hsource (r.toHRun H) H le_rfl

theorem windowPrice7_contracts {A B β t a δ ε : ℝ} {H : ℕ}
    {C : WindowMatrix7} {d : ℕ → ℝ} (data : BandedData7 C d ε)
    (ha : 0<a) (hδ : 0≤δ) (hε : ε=a*δ) (hH : 7≤H)
    (hsource : BandedSource7.{0} A B β t H C d) :
    PriceContracts A B β H t (windowPrice7 data H a t) := by
  intro Y hY
  obtain ⟨D,n,s,k,hk,hkn,h0,h1⟩:=hY
  obtain ⟨r,hx,hv⟩:=s.exists_hRun
  have hs:=windowPrice7_run_step data ha hε hH r k hk (hsource _ r k hk)
  rw [runWindow_eq_segmentWindow s r hx hv k hk (by omega),
    runWindow_eq_segmentWindow s r hx hv (k+1) (by omega) hkn,←h0,←h1] at hs
  have hdrop : Real.exp (-2*t)*windowPrice7 data H a t Y.2≤windowPrice7 data H a t Y.1:=by
    nlinarith [mul_nonneg hδ (sq_nonneg ‖r.x (k-5)‖)]
  have he : Real.exp (2*t)*Real.exp (-2*t)=1:=by rw [←Real.exp_add]; simp
  calc
    windowPrice7 data H a t Y.2=
        Real.exp (2*t)*(Real.exp (-2*t)*windowPrice7 data H a t Y.2):=by
      rw [←mul_assoc,he,one_mul]
    _≤_:=mul_le_mul_of_nonneg_left hdrop (Real.exp_pos _).le

end polyak.FiniteHorizon
