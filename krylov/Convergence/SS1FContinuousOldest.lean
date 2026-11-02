import krylov.Convergence.SS1FContinuousExecution
import krylov.Convergence.WindowSuperlinear
import krylov.Convergence.WindowQueryAsymptotic

/-!
Article: main_krylov, thm:ss1F, continuous-D3 oldest-scale improvement.
Use: the actual oldest corrected diagonal has an arbitrarily small
continuous-Taylor modulus, while all newer observations are negligible
by proved superlinearity of the genuine execution.
Source: the original (S), actual endpoint observations and local continuity
of the true scalar third derivative. No desired recurrence is assumed.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology Asymptotics krylov.Functions krylov.LinearAlgebra
  krylov.Secant krylov.Reference chebyshev1.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n+1))
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace



/-- The actual continuous-D3 corrected matrix error is little-o of the
oldest point of the genuine recursive window, including zero errors. -/
theorem ss1FSequence_continuous_matrix_oldest
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (T : EuclideanSpace ℝ (Fin (n+1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hc : ContinuousOn (fun z=>(T z).form) S)
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
    (fun k=>ss1FNormalizedError f G
      (fun i : Fin (n+1)=>ss1FSequence f G split seed (k+i.val))
      (windowStep (ss1FSequence f G split seed) k)
      (split (fun i=>ss1FSequence f G split seed (k+i.val)))) =o[atTop]
      (fun k=>‖ss1FSequence f G split seed k‖) := by
  let x := ss1FSequence f G split seed
  have hsuper := ss1FSequence_continuous_superlinear f G H T S hS h₀ hnbhd hH₀ hf hG hG₀ hT hc
    split seed hconv hCw hσ hw hind
  have hmono : ∀ᶠ k in atTop,‖x (k+1)‖≤‖x k‖ := by
    simpa only [one_mul,norm_norm] using hsuper.def (by norm_num : (0:ℝ)<1)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hmono
  have htail (k : ℕ) (hk : N≤k) (j : ℕ) : ‖x (k+j)‖≤‖x k‖ := by
    induction j with
    | zero => simp only [Nat.add_zero]; exact le_rfl
    | succ j ih => exact (hN (k+j) (by omega)).trans ih
  refine IsLittleO.of_bound (fun c hcpos=>?_)
  let d : ℝ := ((n+1:ℕ):ℝ)
  have hd : 0<d := by dsimp only [d]; positivity
  let η := c/(2*d)
  have hη : 0<η := div_pos hcpos (by positivity)
  obtain ⟨U,hU,hU₀,hUn,hUS,hmod,hbudget⟩ := continuous_third_source_neighborhood T S hS hnbhd hc hη
  let B := ‖canonicalVariation (T 0)‖+η
  let K := B*(1+2*Cw)+η*(5+2*Cw)
  have hB : 0≤B := by dsimp only [B]; positivity
  have hK : 0≤K := by dsimp only [K]; positivity
  let t := η/(K+1)
  have ht : 0<t := div_pos hη (by positivity)
  have hKt : K*t≤η := by
    have he : (K+1)*t=η := by dsimp only [t]; field_simp
    nlinarith only [he,ht]
  have hdη : d*η=c/2 := by dsimp only [η]; field_simp
  have hsmall : ∀ᶠ k in atTop,‖x (k+1)‖≤t*‖x k‖ := by
    simpa only [norm_norm] using hsuper.def ht
  have hm : ∀ᶠ k in atTop,
      (∀ i : Fin (n+1),x (k+i.val)∈U) ∧
      (∀ i : Fin (n+1),x (k+i.val+1)∈U) ∧x (k+n+1)∈U := by
    have ha (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val)) atTop (𝓝 0) :=
      hconv.comp (tendsto_add_atTop_nat i.val)
    have hb (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val+1)) atTop (𝓝 0) := by
      simpa only [Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
    have hx : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
      simpa only [Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (n+1))
    exact (Filter.eventually_all.mpr fun i=>(ha i).eventually hUn).and
      ((Filter.eventually_all.mpr fun i=>(hb i).eventually hUn).and (hx.eventually hUn))
  filter_upwards [eventually_ge_atTop N,hm,hw,hind,hsmall] with k hk hmk hwk hvk hsk
  let a := fun i : Fin (n+1)=>x (k+i.val)
  let s := windowStep (n:=n+1) x k
  let l := split (fun i=>x (k+i.val))
  have hs (i : Fin (n+1)) : s i≠0 := by
    intro hz
    have hh := windowMatrix_step_ne_zero (unitWindow s) hvk.1 i
    apply hh
    simp only [unitWindow,krylov.Methods.rescaleWindow,hz,smul_zero]
  have ha (i : Fin (n+1)) : ‖a i‖≤‖x k‖ := htail k hk i.val
  have hb (i : Fin (n+1)) : ‖a i+s i‖≤‖x (k+1)‖ := by
    simpa only [a,s,windowStep,add_sub_cancel,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      using htail (k+1) (by omega) i.val
  have hnew (i : Fin (n+1)) (hi : i≠0) : ‖a i‖≤‖x (k+1)‖ := by
    have hip : 0 < i.val := Nat.pos_of_ne_zero (fun hz=>hi (Fin.ext hz))
    convert htail (k+1) (by omega) (i.val-1) using 1
    dsimp only [a]
    congr 2
    omega
  have hx : ‖x (k+n+1)‖≤‖x (k+1)‖ := by
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using htail (k+1) (by omega) n
  have he := ss1F_continuous_newer_error_bound f G H T U hU hU₀ hH₀
    (fun z hz=>hf z (hUS hz)) (fun z hz=>hG z (hUS hz)) (fun z hz=>hT z (hUS hz))
    (hc.mono hUS) hη.le hB hmod hbudget a s l (x (k+n+1)) hmk.1
    (by simpa only [a,s,windowStep,add_sub_cancel,Nat.add_assoc] using hmk.2.1)
    hmk.2.2 (norm_nonneg _) hCw ha hnew hb hx hs
    (by simpa only [a,s,l,windowStep,add_sub_cancel] using hwk)
  change ‖ss1FNormalizedError f G a s l‖≤c*‖‖x k‖‖
  rw [norm_norm]
  apply he.trans
  have hn : K*‖x (k+1)‖≤η*‖x k‖ :=
    (mul_le_mul_of_nonneg_left hsk hK).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hKt (norm_nonneg (x k)))
  have hp := mul_le_mul_of_nonneg_left hn hd.le
  change d*(B*(1+2*Cw)*‖x (k+1)‖+η*(‖x k‖+(5+2*Cw)*‖x (k+1)‖))≤c*‖x k‖
  dsimp only [K] at hp
  have hdq := congrArg (fun z : ℝ=>z*‖x k‖) hdη
  nlinarith only [hp,hdq]


/-- With only continuous D3, the actual SS1-F error is negligible relative
to current error times oldest error. This is the printed continuous branch;
no Lipschitz-third assumption or desired recurrence is present. -/
theorem ss1FSequence_continuous_oldest_product
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (T : EuclideanSpace ℝ (Fin (n+1)) → SymmetricCubic (EuclideanSpace ℝ (Fin (n+1))))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hf : ∀ z∈S,HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z∈S,HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (hT : ∀ z∈S,HasFDerivAt (gradientHessian H) (T z).form z)
    (hc : ContinuousOn (fun z=>(T z).form) S)
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
    (fun k=>ss1FSequence f G split seed (k+n+2)) =o[atTop]
      (fun k=>‖ss1FSequence f G split seed (k+n+1)‖*‖ss1FSequence f G split seed k‖) := by
  let x := ss1FSequence f G split seed
  let a := fun k (i : Fin (n+1))=>x (k+i.val)
  let b := fun k (i : Fin (n+1))=>x (k+i.val+1)
  let s := fun k=>windowStep (n:=n+1) x k
  let l := fun k=>split (fun i=>x (k+i.val))
  let V := fun k=>windowMatrix (unitWindow (s k))
  let X := fun k=>ss1FNormalizedError f G (a k) (s k) (l k)
  let A := fun k=>secantMatrix (averagedDerivative H 0 (x (k+n+1)))
  let q := fun k=>‖x k‖
  have hsuper := ss1FSequence_continuous_superlinear f G H T S hS h₀ hnbhd hH₀ hf hG hG₀ hT hc
    split seed hconv hCw hσ hw hind
  have hX : X =o[atTop] q := ss1FSequence_continuous_matrix_oldest f G H T S hS h₀ hnbhd hH₀
    hf hG hG₀ hT hc split seed hconv hCw hσ hw hind
  have hq : Tendsto q atTop (𝓝 0) := by simpa only [norm_zero] using hconv.norm
  obtain ⟨U,hU,hU₀,hUn,hUS,_hmod,hbudget⟩ :=
    continuous_third_source_neighborhood T S hS hnbhd hc (by norm_num : (0:ℝ)<1)
  let B := ‖canonicalVariation (T 0)‖+1
  have hB : 0≤B := by dsimp only [B]; positivity
  have hH := hessian_lipschitz_of_third_spectral_bound H T U hU
    (fun z hz=>hT z (hUS hz)) hB (by
      intro z hz u hu
      simpa only [hu,mul_one] using hbudget z hz u u u)
  have ha (i : Fin (n+1)) : Tendsto (fun k=>a k i) atTop (𝓝 0) :=
    hconv.comp (tendsto_add_atTop_nat i.val)
  have hb (i : Fin (n+1)) : Tendsto (fun k=>b k i) atTop (𝓝 0) := by
    simpa only [b,x,Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
  have hx : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
    simpa only [x,Nat.add_assoc,Function.comp_def] using hconv.comp (tendsto_add_atTop_nat (n+1))
  have hm : ∀ᶠ k in atTop,(∀ i,a k i∈U) ∧(∀ i,b k i∈U) ∧x (k+n+1)∈U :=
    (Filter.eventually_all.mpr fun i=>(ha i).eventually hUn).and
      ((Filter.eventually_all.mpr fun i=>(hb i).eventually hUn).and (hx.eventually hUn))
  have hA : (fun k=>A k-1) =o[atTop] q := by
    have hbnd : (fun k=>A k-1) =O[atTop] (fun k=>‖x (k+n+1)‖) := by
      apply IsBigO.of_bound (B/2)
      filter_upwards [hm] with k hk
      rw [show ‖A k-1‖=‖averagedDerivative H 0 (x (k+n+1))-ContinuousLinearMap.id ℝ _‖ from
        secantMatrix_sub_one _]
      have hh := secant_operator_endpoint_bound H U hU hU₀ hH 0 (x (k+n+1)) hU₀ hk.2.2
      simpa only [hH₀,norm_zero,zero_add,sub_zero,norm_norm,Real.coe_toNNReal _ hB] using hh
    exact hbnd.trans_isLittleO (superlinear_window_tail x hsuper n)
  have hV : ∀ᶠ k in atTop,‖(V k)⁻¹‖≤σ⁻¹ :=
    hind.mono fun _ h=>inverse_bound_of_leastGain _ h.1 hσ h.2
  have hout := conditioned_model_query_littleo_product V X A (fun k=>x (k+n+1)) q
    (inv_nonneg.mpr hσ.le) hV hq hX hA
  have hs : ∀ᶠ k in atTop,∀ i,s k i≠0 := by
    filter_upwards [hind] with k hk i
    intro hz
    have hh := windowMatrix_step_ne_zero (unitWindow (s k)) hk.1 i
    apply hh
    simp only [unitWindow,krylov.Methods.rescaleWindow,hz,smul_zero]
  apply hout.congr' _ (Filter.Eventually.of_forall fun k=>mul_comm (q k) ‖x (k+n+1)‖)
  filter_upwards [hind,hs,hm] with k hvk hsk hmk
  have hmodel := ss1F_normalized_model_error f G (a k) (s k) (l k) hvk.1
  have hj : inverseCongruence (V k) (ss1FNormalizedModel f G (a k) (s k) (l k))=
      1+inverseCongruence (V k) (X k) := by rw [←hmodel]; abel
  have hrad : cgOperator (A k) (x (k+n+1))=G (x (k+n+1)) := by
    rw [secantMatrix_operator]
    have hp t (ht : t∈Icc (0:ℝ) 1) : (0:E)+t • x (k+n+1)∈U :=
      hU.add_smul_mem hU₀ (by simpa only [zero_add] using hmk.2.2) ht
    have hcont := hH.continuousOn.comp
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
    simpa only [zero_add,hG₀,sub_zero] using
      averagedDerivative_apply G H 0 (x (k+n+1)) hcont (fun t ht=>hG _ (hUS (hp t ht)))
  change _ = x (k+n+2)
  rw [show x (k+n+2)=ss1FPoint f G (a k) (s k) (l k) (x (k+n+1)) from
    ss1FSequence_step f G split seed k]
  rw [ss1FPoint_normalized_model f G (a k) (s k) (l k) (x (k+n+1)) hsk hvk.1,hj,←hrad]
  rfl

end
end krylov.Convergence
