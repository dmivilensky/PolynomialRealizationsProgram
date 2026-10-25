import polyak.FiniteHorizon.KernelRun
import polyak.FiniteHorizon.BlockNearKernel
import polyak.Growth.HorizonPlateau

/-!
Article: Appendix C, strict contraction on the invariant zero-price class.
Use: the proved full finite-memory envelope supplies subexponential growth;
the scalar plateau argument is then applied only to actual zero-price runs.
No rate or Fekete property of a hypothetical restricted class is assumed.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Filter Finset
open scoped Topology

theorem discountedEnergy_subexponential_of_rate_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {A B β T : ℝ} {H : ℕ} (hB : B≠0)
    (r : HRun E A B β H) (hRate : growthRate A B β H≤Real.exp T) :
    Subexponential (discountedEnergy r.x T) := by
  have hlog : Real.log (growthRate A B β H)≤T := by
    simpa only [Real.log_exp] using Real.log_le_log (growthRate_pos A B β H) hRate
  intro δ hδ
  obtain ⟨C,hC,h⟩:=r.discountedEnergy_subexponential hB δ hδ
  refine ⟨C,hC,fun k => ?_⟩
  apply le_trans _ (h k)
  unfold discountedEnergy
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) k])

def KernelWindowEnergyBound (A B β T K : ℝ) (H w : ℕ) (L : WindowPrice H) : Prop :=
  ∀ d : ℕ,∀ r : HRun (EuclideanSpace ℝ (Fin d)) A B β H,ZeroPriceRun L r →
    ∀ i j : ℕ,w ≤ i → i≤j → mass (discountedEnergy r.x T) i (j+1)≤
      K*(energyWindow (discountedEnergy r.x T) w i+energyWindow (discountedEnergy r.x T) w j)

theorem kernelWindowEnergyBound_tail {A B β T K : ℝ} {H w : ℕ}
    (hB : B≠0) (L : WindowPrice H) (hRate : growthRate A B β H≤Real.exp T)
    (hK : 0<K) (henergy : KernelWindowEnergyBound A B β T K H w L) :
    ∃ D : ℝ,1<D ∧ ∀ d : ℕ,∀ r : HRun (EuclideanSpace ℝ (Fin d)) A B β H,
      ZeroPriceRun L r → ∀ i j : ℕ,i≤j → mass (discountedEnergy r.x T) i j≤
        D*(discountedEnergy r.x T i+discountedEnergy r.x T (i+1)) := by
  let C:=(1+2*K)*boundaryConstant A B β T H (2*w+1)
  have hC : 0<C:=mul_pos (by linarith) (boundaryConstant_pos _ _ _ _ _ _)
  let D:=2+C*(1+Real.exp (2*T))
  have hD : 1<D:=by
    dsimp [D]
    nlinarith [mul_pos hC (show 0<1+Real.exp (2*T) by positivity)]
  refine ⟨D,hD,fun d r hr i j hij => ?_⟩
  let q:=r.shift i
  have hsub:=discountedEnergy_subexponential_of_rate_le hB q hRate
  have hmass:=mass_zero_le_boundary (discountedEnergy_nonneg q.x T) hsub hK w
    (fun l hl => henergy d q (hr.shift i) w l le_rfl hl) (j-i)
  have hbound:=q.mass_le_boundaryConstant T (2*w+1)
  have hs : mass (discountedEnergy q.x T) 0 (j-i)≤C*stateNorm q.x 0^2 := by
    calc
      _≤(1+2*K)*mass (discountedEnergy q.x T) 0 (2*w+1):=hmass
      _≤(1+2*K)*(boundaryConstant A B β T H (2*w+1)*stateNorm q.x 0^2):=
        mul_le_mul_of_nonneg_left hbound (by linarith)
      _=_:=by dsimp [C]; ring
  have hshift : mass (discountedEnergy q.x T) 0 (j-i)=
      Real.exp (2*i*T)*mass (discountedEnergy r.x T) i j := by
    change mass (discountedEnergy (fun k => r.x (i+k)) T) 0 (j-i)=_
    rw [mass_discountedEnergy_shift,Nat.add_sub_of_le hij]
  rw [hshift] at hs
  have hcancel : Real.exp (-2*i*T)*Real.exp (2*i*T)=1 := by
    rw [←Real.exp_add]
    have he : -2*(i : ℝ)*T+2*i*T=0:=by ring
    rw [he,Real.exp_zero]
  have hstate : Real.exp (-2*i*T)*stateNorm q.x 0^2=
      discountedEnergy r.x T i+Real.exp (2*T)*discountedEnergy r.x T (i+1) := by
    have hx : stateNorm q.x 0=stateNorm r.x i:=by simp [q,HRun.shift,stateNorm]
    rw [hx,discounted_stateNorm]
  have hb₀:=discountedEnergy_nonneg r.x T i
  have hb₁:=discountedEnergy_nonneg r.x T (i+1)
  calc
    mass (discountedEnergy r.x T) i j=
        Real.exp (-2*i*T)*(Real.exp (2*i*T)*mass (discountedEnergy r.x T) i j):=by
      rw [←mul_assoc,hcancel,one_mul]
    _≤Real.exp (-2*i*T)*(C*stateNorm q.x 0^2):=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _=C*(discountedEnergy r.x T i+Real.exp (2*T)*discountedEnergy r.x T (i+1)):=by
      rw [mul_left_comm,hstate]
    _≤D*(discountedEnergy r.x T i+discountedEnergy r.x T (i+1)):=by
      dsimp [D]
      nlinarith [mul_nonneg (Real.exp_pos (2*T)).le hb₀,mul_nonneg hC.le hb₀,
        mul_nonneg hC.le hb₁,mul_nonneg hC.le (mul_nonneg (Real.exp_pos (2*T)).le hb₀)]

theorem windowTrace_le_discounted_tail {E : Type*} [NormedAddCommGroup E]
    (x : ℕ → E) (T : ℝ) (H m : ℕ) :
    windowTrace x H (H+2*m)≤Real.exp (2*(2*m : ℕ)*T)*
      Real.exp (2*(H+1 : ℕ)*|T|)*mass (discountedEnergy x T) (2*m) (2*m+H+2) := by
  have hterm (i : ℕ) (hi : i∈Icc (2*m) (2*m+H+1)) :
      ‖x i‖^2≤(Real.exp (2*(2*m : ℕ)*T)*Real.exp (2*(H+1 : ℕ)*|T|))*
        discountedEnergy x T i := by
    have hil : (2*m : ℕ) ≤ i :=(mem_Icc.mp hi).1
    have hir : i≤2*m+H+1:=(mem_Icc.mp hi).2
    have hri : (0 : ℝ)≤(i : ℝ)-(2*m : ℕ):=by
      have he : ((2*m : ℕ) : ℝ) ≤ i :=by exact_mod_cast hil
      linarith
    have hrb : (i : ℝ)-(2*m : ℕ)≤(H+1 : ℕ):=by
      have he : (i : ℝ)≤((2*m : ℕ) : ℝ)+(H+1 : ℕ):=by exact_mod_cast hir
      linarith
    have hex : Real.exp (2*(i : ℝ)*T)≤
        Real.exp (2*(2*m : ℕ)*T)*Real.exp (2*(H+1 : ℕ)*|T|) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1:=mul_le_mul_of_nonneg_left (le_abs_self T) hri
      have h2:=mul_le_mul_of_nonneg_right hrb (abs_nonneg T)
      nlinarith
    calc
      ‖x i‖^2=Real.exp (2*(i : ℝ)*T)*discountedEnergy x T i:=by
        unfold discountedEnergy
        rw [←mul_assoc,←Real.exp_add]
        simp
      _≤_:=mul_le_mul_of_nonneg_right hex (discountedEnergy_nonneg x T i)
  calc
    windowTrace x H (H+2*m)=∑ i∈Icc (2*m) (2*m+H+1),‖x i‖^2:=by
      unfold windowTrace
      rw [show H+2*m-H=2*m by omega,show H+2*m+1=2*m+H+1 by omega]
    _≤∑ i∈Icc (2*m) (2*m+H+1),
        (Real.exp (2*(2*m : ℕ)*T)*Real.exp (2*(H+1 : ℕ)*|T|))*discountedEnergy x T i:=
      sum_le_sum hterm
    _=_:=by
      rw [←mul_sum]
      unfold mass
      have he : 2*m+H+2=2*m+H+1+1:=by omega
      rw [he,Ico_add_one_right_eq_Icc]

theorem exists_kernel_trace_contraction {A B β T K : ℝ} {H w : ℕ}
    (hB : B≠0) (L : WindowPrice H) (hRate : growthRate A B β H≤Real.exp T)
    (hpos : PriceNonnegative A B β H L) (hstep : PriceContracts A B β H T L)
    (hK : 0<K) (henergy : KernelWindowEnergyBound A B β T K H w L) :
    ∃ p : ℕ,0<p ∧ ∀ Y∈normalizedEndpointPairs A B β H p,L Y.1=0 →
      traceWindow Y.2<Real.exp (2*(p : ℝ)*T)/2 := by
  obtain ⟨D,hD,hbound⟩:=kernelWindowEnergyBound_tail hB L hRate hK henergy
  let θ:=1-1/D
  have hDp : 0<D:=zero_lt_one.trans hD
  have hθ : 0≤θ:=by
    have hi:=(div_le_one hDp).mpr hD.le
    dsimp [θ]
    linarith
  have hθ1 : θ<1:=by dsimp [θ]; linarith [one_div_pos.mpr hDp]
  let C:=Real.exp (2*(H+1 : ℕ)*|T|)*D*(1+Real.exp (-2*T))
  have hlim : Tendsto (fun m : ℕ => C*θ^m) atTop (𝓝 0) :=by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).const_mul C
  obtain ⟨m,hm,hm0⟩:=((hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))).and
    (eventually_gt_atTop 0)).exists
  refine ⟨2*m,by omega,?_⟩
  intro Y hY hzero
  obtain ⟨s,h0,h1,htr⟩:=normalizedEndpointPairs_sound hB hY
  have hs0 : L (segmentWindow s H)=0:=by rw [←h0]; exact hzero
  obtain ⟨r,hr,hx,hwindows⟩:=exists_zeroPriceRun hB L hpos hstep s (by omega) hs0
  have hinit : windowTrace r.x H H=1 := by
    rw [←trace_runWindow r H le_rfl]
    rw [hwindows H le_rfl (by omega),←h0]
    exact htr
  have hb0 : ‖r.x 0‖^2≤1:=by
    simpa only [hinit] using norm_sq_le_windowTrace r.x (H:=H) (k:=H) (i:=0) (by omega) (by omega)
  have hb1 : ‖r.x 1‖^2≤1:=by
    simpa only [hinit] using norm_sq_le_windowTrace r.x (H:=H) (k:=H) (i:=1) (by omega) (by omega)
  have hpair : discountedEnergy r.x T 0+discountedEnergy r.x T 1≤1+Real.exp (-2*T) := by
    simp only [discountedEnergy,Nat.cast_zero,mul_zero,zero_mul,Real.exp_zero,one_mul,
      Nat.cast_one,mul_one]
    nlinarith [mul_le_mul_of_nonneg_left hb1 (Real.exp_pos (-2*T)).le]
  have htail:=mass_tail_geometric (discountedEnergy_nonneg r.x T) hD (hbound _ r hr)
    m (2*m+H+2) (by omega)
  have hfull:=hbound _ r hr 0 (2*m+H+2) (by omega)
  have hmass : mass (discountedEnergy r.x T) (2*m) (2*m+H+2)≤
      θ^m*D*(1+Real.exp (-2*T)) := by
    calc
      _≤θ^m*mass (discountedEnergy r.x T) 0 (2*m+H+2):=htail
      _≤θ^m*(D*(discountedEnergy r.x T 0+discountedEnergy r.x T 1)):=
        mul_le_mul_of_nonneg_left hfull (pow_nonneg hθ m)
      _≤θ^m*(D*(1+Real.exp (-2*T))):=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpair hDp.le) (pow_nonneg hθ m)
      _=_:=by ring
  have htrace:=windowTrace_le_discounted_tail r.x T H m
  have hfinal : windowTrace r.x H (H+2*m)<Real.exp (2*(2*m : ℕ)*T)/2 := by
    calc
      _≤Real.exp (2*(2*m : ℕ)*T)*Real.exp (2*(H+1 : ℕ)*|T|)*
          (θ^m*D*(1+Real.exp (-2*T))):=
        htrace.trans (mul_le_mul_of_nonneg_left hmass (by positivity))
      _=Real.exp (2*(2*m : ℕ)*T)*(C*θ^m):=by dsimp [C]; ring
      _<_:=by nlinarith [mul_lt_mul_of_pos_left hm (Real.exp_pos (2*(2*m : ℕ)*T))]
  rw [h1,←hwindows (H+2*m) (by omega) le_rfl]
  rw [trace_runWindow r (H+2*m) (by omega)]
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hfinal

end polyak.FiniteHorizon
