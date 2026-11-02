import bezout.Probability.DitherTemporal
import bezout.Models.RidgeSpectral

/-!
Article: bezout, the full fresh-dither ridge oracle and its finite MSE.
Use: actual quantized queries generate their own centered physical error stream;
no martingale or covariance hypothesis is supplied in place of the quantizer.
Proof: strict causality makes each gradient a measurable function of earlier
blocks; the independent fresh-block law supplies its conditional moments.
-/

namespace bezout.Probability.Dither
noncomputable section
open MeasureTheory Polynomial
open scoped BigOperators
variable {N m : ℕ} {J : Type*} [Fintype J]

/-- One quantized gradient call, using the actual worker gradients H y-c_i. -/
def quantizedOracle (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)
    (c : Fin m → EuclideanSpace ℝ J) (h : ℝ)
    (ω : Fin N → (Fin m × J → ℝ)) (s : Fin N) (y : EuclideanSpace ℝ J) :
    EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun j => workerQuantizer m h (fun a => H y a.2-c a.1 a.2) (ω s) j)

/-- Literal nearest-integer quantization is jointly measurable at a nonzero step. -/
theorem quantizer_measurable (h : ℝ) (hh : h≠0) :
    Measurable (fun p : ℝ×ℝ => quantizer h p.1 p.2) := by
  have he : (fun p : ℝ×ℝ => quantizer h p.1 p.2)=
      fun p => p.1+h*normalizedError (p.1/h) p.2 := by
    funext p
    have hx := quantizer_error h p.1 p.2 hh
    linarith
  rw [he]
  exact measurable_fst.add (measurable_const.mul
    (normalizedError_measurable.comp ((measurable_fst.div_const h).prodMk measurable_snd)))

/-- The actual oracle is jointly measurable in its entire tape and current query. -/
theorem quantizedOracle_measurable (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)
    (c : Fin m → EuclideanSpace ℝ J) (h : ℝ) (hh : h≠0) (s : Fin N) :
    Measurable (fun p : (Fin N → (Fin m × J → ℝ))×EuclideanSpace ℝ J =>
      quantizedOracle H c h p.1 s p.2) := by
  have hx (i : Fin m) (j : J) : Measurable
      (fun p : (Fin N → (Fin m × J → ℝ))×EuclideanSpace ℝ J => H p.2 j-c i j) :=
    (((PiLp.proj 2 (𝕜 := ℝ) (fun _ : J => ℝ) j).continuous.comp
      H.toContinuousLinearMap.continuous).measurable.comp measurable_snd).sub measurable_const
  have hu (i : Fin m) (j : J) : Measurable
      (fun p : (Fin N → (Fin m × J → ℝ))×EuclideanSpace ℝ J => p.1 s (i,j)) :=
    (measurable_pi_apply (i,j)).comp ((measurable_pi_apply s).comp measurable_fst)
  have hij (i : Fin m) (j : J) : Measurable
      (fun p : (Fin N → (Fin m × J → ℝ))×EuclideanSpace ℝ J =>
        quantizer h (H p.2 j-c i j) (p.1 s (i,j))) := by
    change Measurable ((fun p : ℝ×ℝ => quantizer h p.1 p.2) ∘
      (fun p : (Fin N → (Fin m × J → ℝ))×EuclideanSpace ℝ J => (H p.2 j-c i j,p.1 s (i,j))))
    exact (quantizer_measurable h hh).comp ((hx i j).prodMk (hu i j))
  have hq (j : J) : Measurable
      (fun p : (Fin N → (Fin m × J → ℝ))×EuclideanSpace ℝ J =>
        (m:ℝ)⁻¹*∑ i : Fin m, quantizer h (H p.2 j-c i j) (p.1 s (i,j))) := by
    have hs : Measurable (fun p : (Fin N → (Fin m × J → ℝ))×EuclideanSpace ℝ J =>
        ∑ i : Fin m, quantizer h (H p.2 j-c i j) (p.1 s (i,j))) := by
      apply Finset.measurable_fun_sum Finset.univ
      intro i _
      exact hij i j
    change Measurable ((fun x : ℝ => (m:ℝ)⁻¹*x) ∘
      (fun p : (Fin N → (Fin m × J → ℝ))×EuclideanSpace ℝ J =>
        ∑ i : Fin m, quantizer h (H p.2 j-c i j) (p.1 s (i,j))))
    exact (measurable_id.const_mul ((m:ℝ)⁻¹)).comp hs

  exact (WithLp.measurable_toLp 2 (J → ℝ)).comp (measurable_pi_iff.mpr hq)

/-- Actual physical quantized queries at each declared oracle call. -/
def quantizedQuery (R : bezout.History N) (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)
    (c : Fin m → EuclideanSpace ℝ J) (h : ℝ) (initial : EuclideanSpace ℝ J)
    (s : Fin N) (ω : Fin N → (Fin m × J → ℝ)) : EuclideanSpace ℝ J :=
  R.oracleQuery initial (quantizedOracle H c h ω) s

/-- Literal finite terminal output of the N-call quantized worker oracle. -/
def quantizedOutput (R : bezout.History N) (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)
    (c : Fin m → EuclideanSpace ℝ J) (h : ℝ) (initial : EuclideanSpace ℝ J)
    (ω : Fin N → (Fin m × J → ℝ)) : EuclideanSpace ℝ J :=
  R.oracleOutput initial (quantizedOracle H c h ω)

/-- Each actual quantized answer is ambient measurable, by strictly causal induction. -/
theorem quantizedAnswers_measurable (R : bezout.History N)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (hh : h≠0) (initial : EuclideanSpace ℝ J) (s : Fin N) :
    Measurable (fun ω => R.oracleAnswers initial (quantizedOracle H c h ω) s) := by
  induction s using (measure (fun s : Fin N => s.val)).wf.induction with
  | h s ih =>
    have he : (fun ω => R.oracleAnswers initial (quantizedOracle H c h ω) s)=
        fun ω => quantizedOracle H c h ω s
          (initial-∑ j, R.a s j • R.oracleAnswers initial (quantizedOracle H c h ω) j) := by
      funext ω
      exact R.oracleAnswers_eq initial _ s
    rw [he]
    have ha (j : Fin N) : Measurable (fun ω =>
        R.a s j • R.oracleAnswers initial (quantizedOracle H c h ω) j) := by
      by_cases hj : j<s
      · exact (ih j hj).const_smul (R.a s j)
      · simp only [R.triangular s j (le_of_not_gt hj),zero_smul]
        exact measurable_const
    have hq : Measurable (fun ω => initial-∑ j,
        R.a s j • R.oracleAnswers initial (quantizedOracle H c h ω) j) :=
      measurable_const.sub (Finset.measurable_fun_sum
        (f := fun j ω => R.a s j • R.oracleAnswers initial (quantizedOracle H c h ω) j)
        Finset.univ (fun j _ => ha j))

    change Measurable ((fun p : (Fin N → (Fin m × J → ℝ))×EuclideanSpace ℝ J =>
      quantizedOracle H c h p.1 s p.2) ∘
      (fun ω => (ω,initial-∑ j, R.a s j • R.oracleAnswers initial (quantizedOracle H c h ω) j)))
    exact (quantizedOracle_measurable H c h hh s).comp (measurable_id.prodMk hq)

/-- Actual query gradients are measurable, without assuming a martingale in advance. -/
theorem quantizedQuery_measurable (R : bezout.History N)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (hh : h≠0) (initial : EuclideanSpace ℝ J) (s : Fin N) :
    Measurable (quantizedQuery R H c h initial s) := by
  change Measurable (fun ω => initial-∑ j, R.a s j • R.oracleAnswers initial (quantizedOracle H c h ω) j)
  exact measurable_const.sub (Finset.measurable_fun_sum
    (f := fun j ω => R.a s j • R.oracleAnswers initial (quantizedOracle H c h ω) j)
    Finset.univ (fun j _ => (quantizedAnswers_measurable R H c h hh initial j).const_smul (R.a s j)))

/-- Equal oracle functions before a call give the same actual query at that call. -/
theorem query_congr_before {E : Type*} [AddCommGroup E] [Module ℝ E]
    (R : bezout.History N) (initial : E) (O₁ O₂ : Fin N → E → E) (s : Fin N)
    (hO : ∀ j, j<s → O₁ j=O₂ j) : R.oracleQuery initial O₁ s=R.oracleQuery initial O₂ s := by
  have ha : ∀ j : Fin N, j<s → R.oracleAnswers initial O₁ j=R.oracleAnswers initial O₂ j := by
    intro j
    induction j using (measure (fun j : Fin N => j.val)).wf.induction with
    | h j ih =>
      intro hj
      rw [R.oracleAnswers_eq,R.oracleAnswers_eq,hO j hj]
      congr 1
      unfold bezout.History.oracleQuery
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k<j
      · rw [ih k hk (hk.trans hj)]
      · simp only [R.triangular j k (le_of_not_gt hk),zero_smul]
  unfold bezout.History.oracleQuery
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j<s
  · rw [ha j hj]
  · simp only [R.triangular s j (le_of_not_gt hj),zero_smul]

/-- The realized physical error is the literal oracle answer minus the exact gradient. -/
def quantizedNoise (R : bezout.History N) (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)
    (c : Fin m → EuclideanSpace ℝ J) (h : ℝ) (initial xstar : EuclideanSpace ℝ J)
    (s : Fin N) (ω : Fin N → (Fin m × J → ℝ)) : EuclideanSpace ℝ J :=
  quantizedOracle H c h ω s (quantizedQuery R H c h initial s ω)-
    H (quantizedQuery R H c h initial s ω-xstar)

/-- The actual worker-quantized trajectory is a genuine centered physical execution. -/
def quantizedExecution (R : bezout.History N) (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)
    (c : Fin m → EuclideanSpace ℝ J) (h : ℝ) (initial xstar : EuclideanSpace ℝ J)
    (ω : Fin N → (Fin m × J → ℝ)) :
    R.Execution H (initial-xstar) (fun s => quantizedNoise R H c h initial xstar s ω) where
  query s := quantizedQuery R H c h initial s ω-xstar
  answer := R.oracleAnswers initial (quantizedOracle H c h ω)
  query_eq s := by
    unfold quantizedQuery bezout.History.oracleQuery
    abel
  answer_eq s := by
    rw [R.oracleAnswers_eq]
    change _=H (quantizedQuery R H c h initial s ω-xstar)+
      (quantizedOracle H c h ω s (quantizedQuery R H c h initial s ω)-H (quantizedQuery R H c h initial s ω-xstar))
    abel

omit [Fintype J] in
/-- Complete physical output equality for the realized quantizer-error stream. -/
theorem quantizedOutput_eq_run (R : bezout.History N) (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)
    (c : Fin m → EuclideanSpace ℝ J) (h : ℝ) (initial xstar : EuclideanSpace ℝ J)
    (ω : Fin N → (Fin m × J → ℝ)) :
    quantizedOutput R H c h initial ω-xstar=
      (R.run H (initial-xstar) (fun s => quantizedNoise R H c h initial xstar s ω)).output := by
  have he := R.execution_unique H (initial-xstar) _
    (quantizedExecution R H c h initial xstar ω) (R.run H (initial-xstar) _)
  rw [← he]
  unfold bezout.History.Execution.output quantizedOutput bezout.History.oracleOutput quantizedExecution
  abel


/-- Actual worker gradients at the actual adaptively chosen physical query. -/
def quantizedGradient (R : bezout.History N) (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)
    (c : Fin m → EuclideanSpace ℝ J) (h : ℝ) (initial : EuclideanSpace ℝ J)
    (s : Fin N) (a : Fin m × J) (ω : Fin N → (Fin m × J → ℝ)) : ℝ :=
  H (quantizedQuery R H c h initial s ω) a.2-c a.1 a.2

/-- The actual gradient at a call is measurable in the dither tape. -/
theorem quantizedGradient_measurable (R : bezout.History N)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (hh : h≠0) (initial : EuclideanSpace ℝ J) (s : Fin N) (a : Fin m × J) :
    Measurable (quantizedGradient R H c h initial s a) :=
  (((PiLp.proj 2 (𝕜 := ℝ) (fun _ : J => ℝ) a.2).continuous.comp
    H.toContinuousLinearMap.continuous).measurable.comp
      (quantizedQuery_measurable R H c h hh initial s)).sub measurable_const

omit [Fintype J] in
/-- Actual quantized queries depend only on blocks strictly before their own call. -/
theorem quantizedQuery_congr (R : bezout.History N)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (initial : EuclideanSpace ℝ J) (s : Fin N)
    (ω ω' : Fin N → (Fin m × J → ℝ)) (hω : ∀ j, j<s → ω j=ω' j) :
    quantizedQuery R H c h initial s ω=quantizedQuery R H c h initial s ω' := by
  apply query_congr_before
  intro j hj
  funext y
  unfold quantizedOracle
  rw [hω j hj]

omit [Fintype J] in
/-- The average of the literal worker gradients is the exact centered objective gradient. -/
theorem workerGradient_mean (hm : 0<m) (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J)
    (c : Fin m → EuclideanSpace ℝ J) (xstar y : EuclideanSpace ℝ J)
    (hc : (m:ℝ)⁻¹ • (∑ i, c i)=H xstar) (j : J) :
    (m:ℝ)⁻¹*∑ i : Fin m, (H y j-c i j)=H (y-xstar) j := by
  have hj := congrArg (fun v : EuclideanSpace ℝ J => v j) hc
  simp only [PiLp.smul_apply,WithLp.ofLp_sum,Finset.sum_apply,smul_eq_mul] at hj
  rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_sub,← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega : m≠0)),one_mul,hj,map_sub]
  rfl

omit [Fintype J] in
/-- The induced error is the literal rounded-worker error at its own actual query. -/
theorem quantizedNoise_workerError (R : bezout.History N) (hm : 0<m)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (initial xstar : EuclideanSpace ℝ J)
    (hc : (m:ℝ)⁻¹ • (∑ i, c i)=H xstar) (s : Fin N)
    (ω : Fin N → (Fin m × J → ℝ)) :
    quantizedNoise R H c h initial xstar s ω=
      workerError m h (quantizedGradient R H c h initial s) (ω,ω s) := by
  ext j
  change workerQuantizer m h (fun a => H (quantizedQuery R H c h initial s ω) a.2-c a.1 a.2) (ω s) j-
      H (quantizedQuery R H c h initial s ω-xstar) j=
    workerQuantizer m h (fun a => H (quantizedQuery R H c h initial s ω) a.2-c a.1 a.2) (ω s) j-
      (m:ℝ)⁻¹*∑ i : Fin m, (H (quantizedQuery R H c h initial s ω) j-c i j)
  rw [workerGradient_mean hm H c xstar _ hc]


omit [Fintype J] in
/-- Masking the future leaves the actual physical query unchanged. -/
theorem quantizedQuery_truncate (R : bezout.History N)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (initial : EuclideanSpace ℝ J) (s : Fin N) (ω : Temporal.Tape N m J) :
    quantizedQuery R H c h initial s ω=
      quantizedQuery R H c h initial s (Temporal.truncate s.val ω) := by
  apply quantizedQuery_congr
  intro j hj
  simp only [Temporal.truncate,Fin.lt_def.mp hj,ite_true]

omit [Fintype J] in
/-- Actual worker gradients are predictable functions of the revealed dither blocks. -/
theorem quantizedGradient_truncate (R : bezout.History N)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (initial : EuclideanSpace ℝ J) (s : Fin N) (a : Fin m × J)
    (ω : Temporal.Tape N m J) :
    quantizedGradient R H c h initial s a ω=
      quantizedGradient R H c h initial s a (Temporal.truncate s.val ω) := by
  unfold quantizedGradient
  rw [quantizedQuery_truncate]

/-- The one actual temporal product tape induces this literal rounded-message error stream. -/
def quantizedStream (R : bezout.History N)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (initial : EuclideanSpace ℝ J) : ℕ → Temporal.Tape N m J → EuclideanSpace ℝ J :=
  Temporal.stream (quantizedGradient R H c h initial) h

omit [Fintype J] in
/-- The constructed temporal stream is the actual physical quantization error at every call. -/
theorem quantizedNoise_eq_stream (R : bezout.History N) (hm : 0<m)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (initial xstar : EuclideanSpace ℝ J)
    (hc : (m:ℝ)⁻¹ • (∑ i, c i)=H xstar) (s : Fin N) (ω : Temporal.Tape N m J) :
    quantizedNoise R H c h initial xstar s ω=quantizedStream R H c h initial s.val ω := by
  rw [quantizedStream,Temporal.stream_at_fin,quantizedNoise_workerError R hm H c h initial xstar hc]
  have he : (fun a => quantizedGradient R H c h initial s a ω)=
      fun a => quantizedGradient R H c h initial s a (Temporal.truncate s.val ω) :=
    funext (fun a => quantizedGradient_truncate R H c h initial s a ω)
  exact congrArg (fun f : Fin m × J → ℝ => WithLp.toLp 2 (fun j =>
    workerQuantizer m h f (ω s) j-(m:ℝ)⁻¹*∑ i : Fin m, f (i,j))) he

/-- The actual quantized trajectory has the exact centered physical-history stochastic output. -/
theorem quantizedOutput_eq_stochastic (R : bezout.History N) (hm : 0<m)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (initial xstar : EuclideanSpace ℝ J)
    (hc : (m:ℝ)⁻¹ • (∑ i, c i)=H xstar) (ω : Temporal.Tape N m J) :
    quantizedOutput R H c h initial ω-xstar=
      R.stochasticOutput H (initial-xstar) (quantizedStream R H c h initial) ω := by
  rw [quantizedOutput_eq_run]
  change (R.run H (initial-xstar) _).output=(R.run H (initial-xstar) _).output
  exact congrArg (fun noise : Fin N → EuclideanSpace ℝ J =>
    (R.run H (initial-xstar) noise).output)
    (funext (fun s => quantizedNoise_eq_stream R hm H c h initial xstar hc s ω))

/-- Conditional centering and adaptation are proved for the actual finite quantizer tape. -/
theorem quantizedStream_martingale (R : bezout.History N)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (hh : h≠0) (initial : EuclideanSpace ℝ J) :
    bezout.Probability.MartingaleDifferences N (Temporal.past N m)
      (quantizedStream R H c h initial) (Temporal.law N m) :=
  Temporal.temporal_martingale _ (quantizedGradient_measurable R H c h hh initial) h hh

/-- The actual N-call quantizer error stream has the exact covariance at each call. -/
theorem quantizedStream_covariance [DecidableEq J] (R : bezout.History N) (hm : 0<m)
    (H : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ J) (c : Fin m → EuclideanSpace ℝ J)
    (h : ℝ) (hh : h≠0) (initial : EuclideanSpace ℝ J) (s : Fin N) :
    covarianceMatrix (quantizedStream R H c h initial s.val) (Temporal.law N m)=
      (h^2/(12*(m:ℝ))) • (1 : Matrix J J ℝ) := by
  rw [quantizedStream,Temporal.stream_at_fin]
  exact Temporal.error_covariance _ (quantizedGradient_measurable R H c h hh initial) hm h hh s

/-- Exact MSE of the literal full quantized-worker oracle trajectory on its actual
finite product tape. No assumed MDS stream replaces the realized quantizer errors. -/
theorem integral_quantizedOutput_covariance [DecidableEq J] (R : bezout.History N) (hm : 0<m)
    (M : Matrix J J ℝ) (c : Fin m → EuclideanSpace ℝ J) (h : ℝ) (hh : h≠0)
    (initial xstar : EuclideanSpace ℝ J)
    (hc : (m:ℝ)⁻¹ • (∑ i, c i)=bezout.History.matrixEnd M xstar) :
    (∫ ω, ‖quantizedOutput R (bezout.History.matrixEnd M) c h initial ω-xstar‖^2
      ∂Temporal.law N m)=
      ‖(aeval (bezout.History.matrixEnd M) R.terminal) (initial-xstar)‖^2+
      ∑ s : Fin N, Matrix.trace
        (aeval M (R.response s)*((h^2/(12*(m:ℝ))) • (1 : Matrix J J ℝ))*(aeval M (R.response s)).transpose) := by
  simp_rw [quantizedOutput_eq_stochastic R hm _ c h initial xstar hc]
  exact R.integral_stochasticOutput_common_covariance _ _
    (quantizedStream_martingale R _ c h hh initial) _
    (quantizedStream_covariance R hm _ c h hh initial)

/-- The printed quantizer step gives the exact intrinsic rank-one ridge MSE for
the actual N-call physical iteration, with arbitrary unit direction and minimizer. -/
theorem integral_quantizedOutput_rankOne [DecidableEq J] (R : bezout.History N) (hm : 0<m)
    (hJ : 0<Fintype.card J) (v : EuclideanSpace ℝ J) (hv : ‖v‖=1)
    (mu L σ : ℝ) (hσ : σ≠0) (c : Fin m → EuclideanSpace ℝ J)
    (initial xstar : EuclideanSpace ℝ J)
    (hc : (m:ℝ)⁻¹ • (∑ i, c i)=bezout.Models.Ridge.spectralMap v mu L xstar) :
    (∫ ω, ‖quantizedOutput R (bezout.Models.Ridge.spectralMap v mu L).toLinearMap
        c (workerStep (J := J) m σ) initial ω-xstar‖^2 ∂Temporal.law N m)=
      (‖initial-xstar‖^2-(inner ℝ v (initial-xstar))^2)*R.terminal.eval mu^2+
      (inner ℝ v (initial-xstar))^2*R.terminal.eval L^2+
      (σ^2/(Fintype.card J:ℝ))*((Fintype.card J-1 : ℕ)*varianceProfile R mu+varianceProfile R L) := by
  have hh := workerStep_ne_zero m hm hJ σ hσ
  simp_rw [quantizedOutput_eq_stochastic R hm _ c _ initial xstar hc]
  apply bezout.Models.Ridge.integral_stochasticOutput_rankOne_covariance R v hv mu L _ _
    (quantizedStream_martingale R _ c _ hh initial)
  intro s
  rw [quantizedStream_covariance R hm _ c _ hh initial s,workerStep_variance m hm]

end
end bezout.Probability.Dither
