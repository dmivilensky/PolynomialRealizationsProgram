import bezout.Probability.DitherWorkers
import bezout.Probability.Martingale

/-!
Article: bezout, fresh worker quantization throughout an actual finite history.
Use: a single finite product dither tape carries its genuine past filtration;
every measurable causal worker-gradient process produces martingale differences
with the exact averaged quantizer covariance at each physical call.
Proof: the past/current-block pair has its actual product law, so the proved
input-dependent fresh rounding law transports to every stage of the same tape.
-/

namespace bezout.Probability.Dither.Temporal
noncomputable section
universe u
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {N m : ℕ} {J : Type*} [Fintype J]

/-- One finite tape of actual worker/component dither blocks. -/
abbrev Tape (N m : ℕ) (J : Type*) := Fin N → (Fin m×J → ℝ)

/-- The single probability law supplies fresh blocks at all physical calls. -/
def law (N m : ℕ) : Measure (Tape N m J) := Measure.pi (fun _ => workerLaw m)

instance (N m : ℕ) : IsProbabilityMeasure (law (J := J) N m) := by
  classical
  unfold law
  infer_instance

/-- The complete revealed past, with every future dither block replaced by zero. -/
def truncate (k : ℕ) (ω : Tape N m J) : Tape N m J :=
  fun j => if j.val<k then ω j else 0

omit [Fintype J] in
/-- The past mask is an actual measurable function of the finite tape. -/
theorem truncate_measurable (k : ℕ) : Measurable (truncate (N := N) (m := m) (J := J) k) := by
  classical
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j.val<k
  · simpa only [truncate,hj,ite_true] using measurable_pi_apply j
  · simp only [truncate,hj,ite_false]
    exact measurable_const

omit [Fintype J] in
/-- Revealing more blocks and then masking the past restores the same past. -/
theorem truncate_comp (s t : ℕ) (hst : s≤t) (ω : Tape N m J) :
    truncate s (truncate t ω)=truncate s ω := by
  funext j
  by_cases hj : j.val<s
  · simp only [truncate,hj,show j.val<t from hj.trans_le hst,ite_true]
  · simp only [truncate,hj,ite_false]

/-- The precise raw-dither filtration before the next actual physical call. -/
def past (N m : ℕ) : Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (Tape N m J)) where
  seq k := MeasurableSpace.comap (truncate k) MeasurableSpace.pi
  mono' s t hst := by
    have he : truncate (N := N) (m := m) (J := J) s=
        (truncate s) ∘ (truncate t) := by funext ω; exact (truncate_comp s t hst ω).symm
    change MeasurableSpace.comap (truncate s) _≤MeasurableSpace.comap (truncate t) _
    rw [he,← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (truncate_measurable s).comap_le
  le' k := (truncate_measurable k).comap_le

omit [Fintype J] in
/-- A revealed block is measurable at every later raw-dither time. -/
theorem eval_measurable_past (s : Fin N) (k : ℕ) (hsk : s.val<k) :
    Measurable[past N m k] (fun ω : Tape N m J => ω s) := by
  have hm := (measurable_pi_apply s).comp
    (comap_measurable (truncate (N := N) (m := m) (J := J) k))
  simpa only [Function.comp_def,truncate,hsk,ite_true] using hm

@[instance_reducible] private def rawPast (N m k : ℕ) : MeasurableSpace (Tape N m J) :=
  ⨆ j : Fin N, ⨆ (_ : j.val<k),
    MeasurableSpace.comap (fun ω : Tape N m J => ω j) MeasurableSpace.pi

/-- The current fresh block is independent of the entire raw past. -/
theorem current_independent_past (s : Fin N) :
    Indep (MeasurableSpace.comap (fun ω : Tape N m J => ω s) MeasurableSpace.pi)
      (past N m s.val) (law N m) := by
  classical
  have hprefix : @Measurable (Tape N m J) (Tape N m J) (rawPast N m s.val) MeasurableSpace.pi
      (truncate s.val) := by
    let : MeasurableSpace (Tape N m J) := rawPast N m s.val
    apply (@measurable_pi_iff (Tape N m J) (Fin N) (fun _ => Fin m×J → ℝ)
      (rawPast N m s.val) (fun _ => MeasurableSpace.pi) (truncate s.val)).mpr
    intro j
    by_cases hj : j.val<s.val
    · simp only [truncate,hj,ite_true]
      exact (comap_measurable (fun ω : Tape N m J => ω j)).mono
        (le_iSup_of_le j (le_iSup_of_le hj le_rfl)) le_rfl
    · simp only [truncate,hj,ite_false]
      exact measurable_const
  have hi := indep_iSup_of_disjoint
    (fun j : Fin N => (measurable_pi_apply j : Measurable (fun ω : Tape N m J => ω j)).comap_le)
    (iIndepFun_pi (μ := fun _ : Fin N => workerLaw (J := J) m)
      (X := fun _ (x : Fin m×J → ℝ) => x) (fun _ => aemeasurable_id))
    (S := {s}) (T := {j : Fin N | j.val<s.val})
    (by simp : Disjoint ({s} : Set (Fin N)) {j | j.val<s.val})
  have hi' : Indep (MeasurableSpace.comap (fun ω : Tape N m J => ω s) MeasurableSpace.pi)
      (rawPast N m s.val) (law N m) := by
    simpa only [iSup_singleton,Set.mem_ofPred_eq,rawPast,law] using hi
  exact indep_of_indep_of_le_right hi' hprefix.comap_le

/-- Actual distribution of the complete masked past. -/
def pastLaw (k : ℕ) : Measure (Tape N m J) :=
  Measure.map (truncate k) (law N m)

instance (k : ℕ) : IsProbabilityMeasure (pastLaw (N := N) (m := m) (J := J) k) := by
  unfold pastLaw
  infer_instance

/-- The masked past and current fresh block have exactly their product law. -/
theorem stagePair_preserving (s : Fin N) :
    MeasurePreserving (fun ω : Tape N m J => (truncate s.val ω,ω s)) (law N m)
      ((pastLaw s.val).prod (workerLaw m)) := by
  have hi : IndepFun (truncate (N := N) (m := m) (J := J) s.val)
      (fun ω : Tape N m J => ω s) (law N m) :=
    (IndepFun_iff_Indep _ _ _).mpr (current_independent_past s).symm
  refine ⟨(truncate_measurable s.val).prodMk (measurable_pi_apply s),?_⟩
  rw [hi.map_prod_eq_prod_map_map (truncate_measurable s.val).aemeasurable
    (measurable_pi_apply s).aemeasurable]
  have he : Measure.map (fun ω : Tape N m J => ω s) (law N m)=workerLaw m :=
    (measurePreserving_eval (fun _ : Fin N => workerLaw (J := J) m) s).map_eq
  rw [he]
  rfl

/-- Per-call worker gradients, before masking unrevealed dither coordinates. -/
abbrev Gradients (N m : ℕ) (J : Type*) := Fin N → Fin m×J → Tape N m J → ℝ

/-- The actual rounded-message error at one call, evaluated on the same finite tape. -/
def error (g : Gradients N m J) (h : ℝ) (s : Fin N) (ω : Tape N m J) : EuclideanSpace ℝ J :=
  workerError m h (g s) (truncate s.val ω,ω s)

/-- The actual induced error stream, zero after its finite physical horizon. -/
def stream (g : Gradients N m J) (h : ℝ) (k : ℕ) (ω : Tape N m J) : EuclideanSpace ℝ J :=
  if hk : k<N then error g h ⟨k,hk⟩ ω else 0

omit [Fintype J] in
/-- The exact rounded error equals its established fresh-block representation. -/
theorem error_eq_fresh (g : Gradients N m J) (h : ℝ) (hh : h≠0) (s : Fin N) :
    error g h s=fun ω => freshAverageNoise m h (g s) (truncate s.val ω,ω s) := by
  funext ω
  exact congrFun (workerError_eq m h hh (g s)) (truncate s.val ω,ω s)

private theorem fresh_error_measurable (g : Gradients N m J)
    (hg : ∀ s a, Measurable (g s a)) (h : ℝ) (s : Fin N) :
    Measurable (freshAverageNoise m h (g s)) :=
  (averageNoise_measurable m h).comp
    (fresh_worker_error_preserving (pastLaw s.val) m (fun a ω => g s a ω/h)
      (fun a => (hg s a).div_const h)).measurable

/-- The actual stage error is measurable immediately after that physical call. -/
theorem error_adapted (g : Gradients N m J) (hg : ∀ s a, Measurable (g s a))
    (h : ℝ) (hh : h≠0) (s : Fin N) :
    StronglyMeasurable[past N m (s.val+1)] (error g h s) := by
  rw [error_eq_fresh g h hh s]
  have ht : @Measurable (Tape N m J) (Tape N m J) (past N m (s.val+1)) MeasurableSpace.pi
      (truncate s.val) :=
    (comap_measurable (truncate (N := N) (m := m) (J := J) s.val)).mono
      ((past N m).mono (Nat.le_succ s.val)) le_rfl
  exact ((fresh_error_measurable g hg h s).comp
    (ht.prodMk (eval_measurable_past s (s.val+1) (Nat.lt_succ_self s.val)))).stronglyMeasurable

/-- The actual finite-tape stage error is square integrable. -/
theorem error_memLp (g : Gradients N m J) (hg : ∀ s a, Measurable (g s a))
    (h : ℝ) (hh : h≠0) (s : Fin N) : MemLp (error g h s) 2 (law N m) := by
  rw [error_eq_fresh g h hh s]
  exact (freshAverageNoise_memLp (pastLaw s.val) m h (g s) (hg s)).comp_measurePreserving
    (stagePair_preserving s)

/-- Its unconditional mean is exactly zero under the single full-tape law. -/
theorem error_mean (g : Gradients N m J) (hg : ∀ s a, Measurable (g s a))
    (h : ℝ) (hh : h≠0) (s : Fin N) :
    (∫ ω, error g h s ω ∂law N m)=0 := by
  rw [error_eq_fresh g h hh s]
  have hp := stagePair_preserving (m := m) (J := J) s
  have hi := integral_map (μ := law N m) hp.measurable.aemeasurable
    (f := freshAverageNoise m h (g s)) (by
      rw [hp.map_eq]
      exact (fresh_error_measurable g hg h s).aestronglyMeasurable)
  rw [hp.map_eq] at hi
  exact hi.symm.trans (freshAverageNoise_mean (pastLaw s.val) m h (g s) (hg s))

omit [Fintype J] in
private theorem indep_pullback {A B C D : Type u} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] {μ : Measure A} {ν : Measure B}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {T : A → B}
    (hT : MeasurePreserving T μ ν) {X : B → C} {Y : B → D}
    (hX : Measurable X) (hY : Measurable Y) (hi : IndepFun X Y ν) :
    IndepFun (fun a => X (T a)) (fun a => Y (T a)) μ := by
  have hm {V : Type u} [MeasurableSpace V] (Z : B → V) (hZ : Measurable Z) :
      Measure.map (fun a => Z (T a)) μ=Measure.map Z ν := by
    change Measure.map (Z ∘ T) μ=Measure.map Z ν
    rw [← Measure.map_map hZ hT.measurable,hT.map_eq]
  apply (indepFun_iff_map_prod_eq_prod_map_map (hX.comp hT.measurable).aemeasurable
    (hY.comp hT.measurable).aemeasurable).mpr
  change Measure.map (fun a => (X (T a),Y (T a))) μ=
    (Measure.map (fun a => X (T a)) μ).prod (Measure.map (fun a => Y (T a)) μ)
  rw [hm _ (hX.prodMk hY),hm X hX,hm Y hY]
  exact hi.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable

/-- The realized adaptive rounded error is independent of the complete tape past. -/
theorem error_independent_past (g : Gradients N m J) (hg : ∀ s a, Measurable (g s a))
    (h : ℝ) (hh : h≠0) (s : Fin N) :
    Indep (MeasurableSpace.comap (error g h s) inferInstance) (past N m s.val) (law N m) := by
  rw [error_eq_fresh g h hh s]
  have hi := indep_pullback (stagePair_preserving (m := m) (J := J) s)
    measurable_fst (fresh_error_measurable g hg h s)
    (freshAverageNoise_independent (pastLaw s.val) m h (g s) (hg s))
  exact (IndepFun_iff_Indep _ _ _).mp hi.symm

/-- Conditional centering of actual rounded errors over the entire finite execution. -/
theorem error_centered (g : Gradients N m J) (hg : ∀ s a, Measurable (g s a))
    (h : ℝ) (hh : h≠0) (s : Fin N) :
    (law N m)[error g h s | past N m s.val] =ᵐ[law N m] fun _ => (0 : EuclideanSpace ℝ J) := by
  have hm : Measurable (error g h s) :=
    (error_adapted g hg h hh s).measurable.mono ((past N m).le _) le_rfl
  have he := condExp_indep_eq hm.comap_le ((past N m).le s.val)
    (comap_measurable (error g h s)).stronglyMeasurable (error_independent_past g hg h hh s)
  simpa only [error_mean g hg h hh s] using he

/-- A single actual finite dither tape gives the article's full temporal MDS model. -/
theorem temporal_martingale (g : Gradients N m J) (hg : ∀ s a, Measurable (g s a))
    (h : ℝ) (hh : h≠0) :
    bezout.Probability.MartingaleDifferences N (past N m) (stream g h) (law N m) where
  adapted s hs := by
    have he : stream g h s=error g h ⟨s,hs⟩ := by funext ω; simp only [stream,hs,dite_true]
    rw [he]
    exact error_adapted g hg h hh ⟨s,hs⟩
  squareIntegrable s hs := by
    have he : stream g h s=error g h ⟨s,hs⟩ := by funext ω; simp only [stream,hs,dite_true]
    rw [he]
    exact error_memLp g hg h hh ⟨s,hs⟩
  centered s hs := by
    have he : stream g h s=error g h ⟨s,hs⟩ := by funext ω; simp only [stream,hs,dite_true]
    rw [he]
    exact error_centered g hg h hh ⟨s,hs⟩

omit [Fintype J] in
/-- Finite physical slots of the extended stream are exactly the realized errors. -/
@[simp] theorem stream_at_fin (g : Gradients N m J) (h : ℝ) (s : Fin N) :
    stream g h s.val=error g h s := by
  funext ω
  simp only [stream,s.isLt,dite_true]

/-- Every actual temporal covariance entry has the same input-independent value. -/
theorem error_cross [DecidableEq J] (g : Gradients N m J)
    (hg : ∀ s a, Measurable (g s a)) (hm : 0<m) (h : ℝ) (hh : h≠0)
    (s : Fin N) (j k : J) :
    (∫ ω, error g h s ω j*error g h s ω k ∂law N m)=
      if j=k then h^2/(12*(m:ℝ)) else 0 := by
  rw [error_eq_fresh g h hh s]
  have hp := stagePair_preserving (m := m) (J := J) s
  have hi := integral_map (μ := law N m) hp.measurable.aemeasurable
    (f := fun p => freshAverageNoise m h (g s) p j*freshAverageNoise m h (g s) p k) (by
      rw [hp.map_eq]
      exact (coordinate_mul_integrable (freshAverageNoise_memLp (pastLaw s.val) m h (g s) (hg s)) j k).aestronglyMeasurable)
  rw [hp.map_eq] at hi
  exact hi.symm.trans (freshAverageNoise_cross (pastLaw s.val) m hm h (g s) (hg s) j k)

/-- The covariance of each realized tape error is exactly h²/(12m) times identity. -/
theorem error_covariance [DecidableEq J] (g : Gradients N m J)
    (hg : ∀ s a, Measurable (g s a)) (hm : 0<m) (h : ℝ) (hh : h≠0) (s : Fin N) :
    covarianceMatrix (error g h s) (law N m)=(h^2/(12*(m:ℝ))) • (1 : Matrix J J ℝ) := by
  rw [covarianceMatrix_of_mean_zero _ (error_mean g hg h hh s)]
  ext j k
  simp only [secondMomentMatrix,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  rw [error_cross g hg hm h hh s]
  split_ifs <;> simp

/-- Exact conditional covariance entries hold at every physical time of the same tape. -/
theorem error_conditional_cross [DecidableEq J] (g : Gradients N m J)
    (hg : ∀ s a, Measurable (g s a)) (hm : 0<m) (h : ℝ) (hh : h≠0)
    (s : Fin N) (j k : J) :
    (law N m)[(fun ω => error g h s ω j*error g h s ω k) | past N m s.val] =ᵐ[law N m]
      fun _ => if j=k then h^2/(12*(m:ℝ)) else 0 := by
  have hi : IndepFun (error g h s) (truncate (N := N) (m := m) (J := J) s.val) (law N m) :=
    (IndepFun_iff_Indep _ _ _).mpr (error_independent_past g hg h hh s)
  have hF : Measurable (fun v : EuclideanSpace ℝ J => v j*v k) := by fun_prop
  have hmerror : Measurable (error g h s) :=
    (error_adapted g hg h hh s).measurable.mono ((past N m).le _) le_rfl
  have he := condExp_indep_eq (hF.comp hmerror).comap_le ((past N m).le s.val)
    (comap_measurable (fun ω => error g h s ω j*error g h s ω k)).stronglyMeasurable
    ((IndepFun_iff_Indep _ _ _).mp (hi.comp hF measurable_id))
  simpa only [error_cross g hg hm h hh s j k] using he

/-- Exact unconditional physical error energy at any time of the full finite run. -/
theorem error_integral_norm_sq [DecidableEq J] (g : Gradients N m J)
    (hg : ∀ s a, Measurable (g s a)) (hm : 0<m) (h : ℝ) (hh : h≠0) (s : Fin N) :
    (∫ ω, ‖error g h s ω‖^2 ∂law N m)=(Fintype.card J:ℝ)*(h^2/(12*(m:ℝ))) := by
  have hf (ω : Tape N m J) : ‖error g h s ω‖^2=
      ∑ j : J, error g h s ω j*error g h s ω j := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [pow_two]
  calc
    _ = ∫ ω, ∑ j : J, error g h s ω j*error g h s ω j ∂law N m :=
      integral_congr_ae (Filter.Eventually.of_forall hf)
    _ = ∑ j : J, ∫ ω, error g h s ω j*error g h s ω j ∂law N m :=
      integral_finsetSum Finset.univ (fun j _ =>
        coordinate_mul_integrable (error_memLp g hg h hh s) j j)
    _ = _ := by
      simp only [error_cross g hg hm h hh s,ite_true,Finset.sum_const,
        Finset.card_univ,nsmul_eq_mul]

/-- The exact conditional physical variance budget is realized at every oracle call. -/
theorem error_conditional_norm_sq [DecidableEq J] (g : Gradients N m J)
    (hg : ∀ s a, Measurable (g s a)) (hm : 0<m) (h : ℝ) (hh : h≠0) (s : Fin N) :
    (law N m)[(fun ω => ‖error g h s ω‖^2) | past N m s.val] =ᵐ[law N m]
      fun _ => (Fintype.card J:ℝ)*(h^2/(12*(m:ℝ))) := by
  have hi : IndepFun (error g h s) (truncate (N := N) (m := m) (J := J) s.val) (law N m) :=
    (IndepFun_iff_Indep _ _ _).mpr (error_independent_past g hg h hh s)
  have hF : Measurable (fun v : EuclideanSpace ℝ J => ‖v‖^2) := by fun_prop
  have hmerror : Measurable (error g h s) :=
    (error_adapted g hg h hh s).measurable.mono ((past N m).le _) le_rfl
  have he := condExp_indep_eq (hF.comp hmerror).comap_le ((past N m).le s.val)
    (comap_measurable (fun ω => ‖error g h s ω‖^2)).stronglyMeasurable
    ((IndepFun_iff_Indep _ _ _).mp (hi.comp hF measurable_id))
  simpa only [error_integral_norm_sq g hg hm h hh s] using he

end
end bezout.Probability.Dither.Temporal
