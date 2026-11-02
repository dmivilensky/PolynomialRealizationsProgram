import bezout.Probability.DitherFresh
import bezout.Probability.Covariance
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Independence.Integration

/-!
Article: bezout, distributed subtractive-dither quantization and Appendix D.
Use: independent fresh worker/component dithers produce the actual averaged
quantizer error with covariance h²/(12m) I, including past-dependent inputs.
Proof: the finite product law preserves the complete rounded error block;
coordinate independence removes cross terms and averaging supplies 1/m.
-/

namespace bezout.Probability.Dither
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {J : Type*} [Fintype J]

/-- One fresh dither for each worker and each vector component. -/
def workerLaw (m : ℕ) : Measure (Fin m × J → ℝ) := Measure.pi (fun _ => law)

instance (m : ℕ) : IsProbabilityMeasure (workerLaw (J := J) m) := by
  classical
  unfold workerLaw
  infer_instance

/-- The whole rounded error block, before the physical scaling by h. -/
def workerTransform (m : ℕ) (g : Fin m × J → ℝ) (u : Fin m × J → ℝ) : Fin m × J → ℝ :=
  fun a => normalizedError (g a) (u a)

/-- All worker/component errors jointly retain their independent uniform law. -/
theorem workerTransform_preserving (m : ℕ) (g : Fin m × J → ℝ) :
    MeasurePreserving (workerTransform m g) (workerLaw m) (workerLaw m) :=
  measurePreserving_pi _ _ (fun a => normalizedError_preserving (g a))

/-- Literal independent-worker averaged quantizer output, component by component. -/
def workerQuantizer (m : ℕ) (h : ℝ) (g u : Fin m × J → ℝ) (j : J) : ℝ :=
  (m:ℝ)⁻¹*∑ i : Fin m, quantizer h (g (i,j)) (u (i,j))

/-- The Euclidean noise vector obtained by averaging an independent error block. -/
def averageNoise (m : ℕ) (h : ℝ) (u : Fin m × J → ℝ) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun j => (h/(m:ℝ))*∑ i : Fin m, u (i,j))

omit [Fintype J] in
/-- The literal quantizer error is exactly the averaged transformed block. -/
theorem workerQuantizer_error (m : ℕ) (h : ℝ) (hh : h≠0)
    (g u : Fin m × J → ℝ) (j : J) :
    workerQuantizer m h g u j-(m:ℝ)⁻¹*∑ i : Fin m, g (i,j)=
      averageNoise m h (workerTransform m (fun a => g a/h) u) j := by
  classical
  change (m:ℝ)⁻¹*(∑ i : Fin m, quantizer h (g (i,j)) (u (i,j)))-
    (m:ℝ)⁻¹*(∑ i : Fin m, g (i,j))=(h/(m:ℝ))*∑ i : Fin m, normalizedError (g (i,j)/h) (u (i,j))
  rw [← mul_sub,← Finset.sum_sub_distrib]
  simp_rw [quantizer_error h _ _ hh]
  rw [← Finset.mul_sum]
  ring

/-- Each coordinate of the product block has the centered uniform second moment. -/
theorem worker_coordinate_mean (m : ℕ) (a : Fin m × J) :
    (∫ u, u a ∂workerLaw m)=0 := by
  classical
  rw [workerLaw,integral_eval]
  exact integral_id

/-- Each coordinate has exactly variance one over twelve. -/
theorem worker_coordinate_square (m : ℕ) (a : Fin m × J) :
    (∫ u, (u a)^2 ∂workerLaw m)=(1/12:ℝ) := by
  classical
  exact (integral_comp_eval (μ := fun _ : Fin m × J => law) (i := a)
    (f := fun x : ℝ => x^2) (by fun_prop)).trans integral_square

/-- The compact uniform coordinate is square integrable. -/
theorem uniform_memLp : MemLp (fun x : ℝ => x) 2 law := by
  classical
  apply memLp_of_bounded (a := -(1/2:ℝ)) (b := 1/2) _ (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact ⟨hx.1.le,hx.2⟩

/-- Every physical worker coordinate is square integrable under the finite product law. -/
theorem worker_coordinate_memLp (m : ℕ) (a : Fin m × J) :
    MemLp (fun u => u a) 2 (workerLaw m) :=
  uniform_memLp.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m × J => law) a)

/-- Distinct worker/component pairs have zero cross moment. -/
theorem worker_coordinate_cross [DecidableEq J] (m : ℕ) (a b : Fin m × J) :
    (∫ u, u a*u b ∂workerLaw m)=if a=b then (1/12:ℝ) else 0 := by
  classical
  by_cases hab : a=b
  · subst b
    simp only [ite_true,← sq]
    exact worker_coordinate_square m a
  · rw [ite_eq_right hab]
    have hi := (iIndepFun_pi (μ := fun _ : Fin m × J => law)
      (X := fun _ (x : ℝ) => x) (fun _ => aemeasurable_id)).indepFun hab
    change IndepFun (fun u : Fin m × J → ℝ => u a) (fun u => u b) (workerLaw m) at hi
    rw [hi.integral_fun_mul_eq_mul_integral
      (worker_coordinate_memLp m a).aestronglyMeasurable (worker_coordinate_memLp m b).aestronglyMeasurable,
      worker_coordinate_mean,worker_coordinate_mean,mul_zero]

/-- Averaging gives a genuinely square-integrable Euclidean noise vector. -/
theorem averageNoise_memLp (m : ℕ) (h : ℝ) : MemLp (averageNoise (J := J) m h) 2 (workerLaw m) := by
  classical
  apply MemLp.of_eval_piLp
  intro j
  exact (memLp_finsetSum Finset.univ (fun i _ => worker_coordinate_memLp m (i,j))).const_mul _

/-- The averaged worker error has zero Bochner mean. -/
theorem averageNoise_mean (m : ℕ) (h : ℝ) :
    (∫ u, averageNoise (J := J) m h u ∂workerLaw m)=0 := by
  classical
  ext j
  rw [eval_integral_piLp (fun k => ((averageNoise_memLp m h).eval_piLp k).integrable (by norm_num))]
  change (∫ u, (h/(m:ℝ))*∑ i : Fin m, u (i,j) ∂workerLaw m)=0
  rw [integral_const_mul,integral_finsetSum]
  · simp only [worker_coordinate_mean,Finset.sum_const_zero,mul_zero]
  · intro i _
    exact (worker_coordinate_memLp m (i,j)).integrable (by norm_num)

/-- The exact coordinate second moments after averaging over workers. -/
theorem averageNoise_cross [DecidableEq J] (m : ℕ) (hm : 0<m) (h : ℝ) (j k : J) :
    (∫ u, averageNoise m h u j*averageNoise m h u k ∂workerLaw m)=
      if j=k then h^2/(12*(m:ℝ)) else 0 := by
  classical
  change (∫ u, ((h/(m:ℝ))*∑ i : Fin m, u (i,j))*
    ((h/(m:ℝ))*∑ l : Fin m, u (l,k)) ∂workerLaw m)=_
  simp_rw [show ∀ a b : ℝ, ((h/(m:ℝ))*a)*((h/(m:ℝ))*b)=(h/(m:ℝ))^2*(a*b) by intros; ring]
  rw [integral_const_mul]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  have hi (i : Fin m) : Integrable (fun u => ∑ l : Fin m, u (i,j)*u (l,k)) (workerLaw m) :=
    integrable_finsetSum _ (fun l _ =>
      (worker_coordinate_memLp m (i,j)).integrable_mul (worker_coordinate_memLp m (l,k)))
  have hs (i : Fin m) :
      (∫ u, ∑ l : Fin m, u (i,j)*u (l,k) ∂workerLaw m)=
        ∑ l : Fin m, ∫ u, u (i,j)*u (l,k) ∂workerLaw m :=
    integral_finsetSum _ (fun l _ =>
      (worker_coordinate_memLp m (i,j)).integrable_mul (worker_coordinate_memLp m (l,k)))
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp_rw [hs,worker_coordinate_cross]
  by_cases hjk : j=k
  · subst k
    simp only [Prod.mk.injEq,and_true,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hn : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  · simp [hjk]

/-- Actual covariance is h²/(12m) times the identity, not merely a diagonal bound. -/
theorem averageNoise_covariance [DecidableEq J] (m : ℕ) (hm : 0<m) (h : ℝ) :
    covarianceMatrix (averageNoise (J := J) m h) (workerLaw m)=
      (h^2/(12*(m:ℝ))) • (1 : Matrix J J ℝ) := by
  classical
  rw [covarianceMatrix_of_mean_zero _ (averageNoise_mean m h)]
  ext j k
  simp only [secondMomentMatrix,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  rw [averageNoise_cross m hm]
  split_ifs <;> simp


omit [Fintype J] in
/-- Averaging a block is a measurable Euclidean vector-valued map. -/
theorem averageNoise_measurable (m : ℕ) (h : ℝ) : Measurable (averageNoise (J := J) m h) := by
  unfold averageNoise
  fun_prop

/-- Two scalar inputs jointly determine a measurable rounding error. -/
theorem normalizedError_measurable : Measurable (fun p : ℝ×ℝ => normalizedError p.1 p.2) := by
  change Measurable (fun p : ℝ×ℝ => representative ((-(p.1+p.2):ℝ) : AddCircle (1:ℝ)))
  exact representative_preserving.measurable.comp
    (AddCircle.measurable_mk'.comp ((measurable_fst.add measurable_snd).neg))

section Fresh
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A fresh independent block preserves its joint law with the entire past. -/
theorem fresh_worker_preserving (m : ℕ) (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) :
    MeasurePreserving (fun p : Ω×(Fin m × J → ℝ) =>
      (p.1,workerTransform m (fun a => g a p.1) p.2))
      (μ.prod (workerLaw m)) (μ.prod (workerLaw m)) := by
  have hgm : Measurable (fun p : Ω×(Fin m × J → ℝ) => workerTransform m (fun a => g a p.1) p.2) := by
    apply measurable_pi_iff.mpr
    intro a
    exact normalizedError_measurable.comp
      (((hg a).comp measurable_fst).prodMk ((measurable_pi_apply a).comp measurable_snd))
  have he := (MeasurePreserving.id μ).skew_product
    (g := fun ω u => workerTransform m (fun a => g a ω) u) (μc := workerLaw m) (μd := workerLaw m) hgm
    (Filter.Eventually.of_forall (fun ω => (workerTransform_preserving m (fun a => g a ω)).map_eq))
  simpa only [id_eq] using he

/-- The complete adaptive physical error block has the original independent product law. -/
theorem fresh_worker_error_preserving (m : ℕ) (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) :
    MeasurePreserving (fun p : Ω×(Fin m × J → ℝ) => workerTransform m (fun a => g a p.1) p.2)
      (μ.prod (workerLaw m)) (workerLaw m) :=
  (measurePreserving_snd (μ := μ) (ν := workerLaw m)).comp (fresh_worker_preserving μ m g hg)

/-- The complete adaptive error block is independent of the entire previous history. -/
theorem fresh_worker_independent (m : ℕ) (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) :
    IndepFun (Prod.fst : Ω×(Fin m × J → ℝ) → Ω)
      (fun p => workerTransform m (fun a => g a p.1) p.2) (μ.prod (workerLaw m)) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable
    (fresh_worker_error_preserving μ m g hg).measurable.aemeasurable).mpr
  rw [(fresh_worker_preserving μ m g hg).map_eq,
    (measurePreserving_fst (μ := μ) (ν := workerLaw m)).map_eq,
    (fresh_worker_error_preserving μ m g hg).map_eq]

/-- The actual averaged worker error for arbitrary measurable past-dependent gradients. -/
def freshAverageNoise (m : ℕ) (h : ℝ) (g : Fin m × J → Ω → ℝ)
    (p : Ω×(Fin m × J → ℝ)) : EuclideanSpace ℝ J :=
  averageNoise m h (workerTransform m (fun a => g a p.1/h) p.2)

omit [Fintype J] [MeasurableSpace Ω] in
/-- This error vector is exactly the averaged literal rounded worker messages minus
those workers' average gradient; no ideal noise variable is substituted. -/
theorem freshAverageNoise_actual (m : ℕ) (h : ℝ) (hh : h≠0)
    (g : Fin m × J → Ω → ℝ) (p : Ω×(Fin m × J → ℝ)) (j : J) :
    freshAverageNoise m h g p j=workerQuantizer m h (fun a => g a p.1) p.2 j-
      (m:ℝ)⁻¹*∑ i : Fin m, g (i,j) p.1 :=
  (workerQuantizer_error m h hh _ p.2 j).symm

/-- The actual averaged error is square integrable despite arbitrary adaptive gradients. -/
theorem freshAverageNoise_memLp (m : ℕ) (h : ℝ) (g : Fin m × J → Ω → ℝ)
    (hg : ∀ a, Measurable (g a)) : MemLp (freshAverageNoise m h g) 2 (μ.prod (workerLaw m)) :=
  (averageNoise_memLp m h).comp_measurePreserving
    (fresh_worker_error_preserving μ m (fun a ω => g a ω/h) (fun a => (hg a).div_const h))

/-- Fresh adaptive worker averaging has zero Bochner mean. -/
theorem freshAverageNoise_mean (m : ℕ) (h : ℝ) (g : Fin m × J → Ω → ℝ)
    (hg : ∀ a, Measurable (g a)) :
    (∫ p, freshAverageNoise m h g p ∂μ.prod (workerLaw m))=0 := by
  have he := fresh_worker_error_preserving μ m (fun a ω => g a ω/h) (fun a => (hg a).div_const h)
  have hi := integral_map (μ := μ.prod (workerLaw m)) he.measurable.aemeasurable
    (f := averageNoise m h) (by rw [he.map_eq]; exact (averageNoise_measurable m h).aestronglyMeasurable)
  rw [he.map_eq] at hi
  exact hi.symm.trans (averageNoise_mean m h)

/-- The exact adaptive coordinate cross moments are independent of every input gradient. -/
theorem freshAverageNoise_cross [DecidableEq J] (m : ℕ) (hm : 0<m) (h : ℝ)
    (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) (j k : J) :
    (∫ p, freshAverageNoise m h g p j*freshAverageNoise m h g p k ∂μ.prod (workerLaw m))=
      if j=k then h^2/(12*(m:ℝ)) else 0 := by
  have he := fresh_worker_error_preserving μ m (fun a ω => g a ω/h) (fun a => (hg a).div_const h)
  have hi := integral_map (μ := μ.prod (workerLaw m)) he.measurable.aemeasurable
    (f := fun u => averageNoise m h u j*averageNoise m h u k) (by
      rw [he.map_eq]
      exact (coordinate_mul_integrable (averageNoise_memLp m h) j k).aestronglyMeasurable)
  rw [he.map_eq] at hi
  exact hi.symm.trans (averageNoise_cross m hm h j k)

/-- The actual adaptive worker error covariance is h²/(12m) I. -/
theorem freshAverageNoise_covariance [DecidableEq J] (m : ℕ) (hm : 0<m) (h : ℝ)
    (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) :
    covarianceMatrix (freshAverageNoise m h g) (μ.prod (workerLaw m))=
      (h^2/(12*(m:ℝ))) • (1 : Matrix J J ℝ) := by
  rw [covarianceMatrix_of_mean_zero _ (freshAverageNoise_mean μ m h g hg)]
  ext j k
  simp only [secondMomentMatrix,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
  rw [freshAverageNoise_cross μ m hm h g hg]
  split_ifs <;> simp


/-- The actual averaged quantization error is independent of the complete past. -/
theorem freshAverageNoise_independent (m : ℕ) (h : ℝ) (g : Fin m × J → Ω → ℝ)
    (hg : ∀ a, Measurable (g a)) :
    IndepFun (Prod.fst : Ω×(Fin m × J → ℝ) → Ω) (freshAverageNoise m h g)
      (μ.prod (workerLaw m)) :=
  (fresh_worker_independent μ m (fun a ω => g a ω/h) (fun a => (hg a).div_const h)).comp
    measurable_id (averageNoise_measurable m h)

/-- Conditional centering of the actual Euclidean worker-averaged quantizer error. -/
theorem freshAverageNoise_conditional_mean (m : ℕ) (h : ℝ) (g : Fin m × J → Ω → ℝ)
    (hg : ∀ a, Measurable (g a)) :
    (μ.prod (workerLaw m))[freshAverageNoise m h g |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Ω)] =ᵐ[μ.prod (workerLaw m)]
      fun _ => (0 : EuclideanSpace ℝ J) := by
  have hm : Measurable (freshAverageNoise m h g) :=
    (averageNoise_measurable m h).comp
      (fresh_worker_error_preserving μ m (fun a ω => g a ω/h) (fun a => (hg a).div_const h)).measurable
  have he := condExp_indep_eq hm.comap_le measurable_fst.comap_le
    (comap_measurable (freshAverageNoise m h g)).stronglyMeasurable
    (freshAverageNoise_independent μ m h g hg).symm
  simpa only [freshAverageNoise_mean μ m h g hg] using he

/-- Every conditional covariance entry is h²/(12m) times the identity entry. -/
theorem freshAverageNoise_conditional_cross [DecidableEq J] (m : ℕ) (hm : 0<m) (h : ℝ)
    (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) (j k : J) :
    (μ.prod (workerLaw m))[(fun p => freshAverageNoise m h g p j*freshAverageNoise m h g p k) |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Ω)] =ᵐ[μ.prod (workerLaw m)]
      fun _ => if j=k then h^2/(12*(m:ℝ)) else 0 := by
  have hf : Measurable (fun v : EuclideanSpace ℝ J => v j*v k) := by fun_prop
  have he0 := (freshAverageNoise_independent μ m h g hg).comp measurable_id hf
  have hm0 : Measurable (fun p => freshAverageNoise m h g p j*freshAverageNoise m h g p k) :=
    hf.comp ((averageNoise_measurable m h).comp
      (fresh_worker_error_preserving μ m (fun a ω => g a ω/h) (fun a => (hg a).div_const h)).measurable)
  have he := condExp_indep_eq hm0.comap_le measurable_fst.comap_le
    (comap_measurable (fun p => freshAverageNoise m h g p j*freshAverageNoise m h g p k)).stronglyMeasurable
    he0.symm
  simpa only [freshAverageNoise_cross μ m hm h g hg j k] using he


/-- The exact conditional squared norm budget of actual worker-averaged errors. -/
theorem freshAverageNoise_conditional_norm_sq [DecidableEq J] (m : ℕ) (hm : 0<m) (h : ℝ)
    (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) :
    (μ.prod (workerLaw m))[(fun p => ‖freshAverageNoise m h g p‖^2) |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Ω)] =ᵐ[μ.prod (workerLaw m)]
      fun _ => (Fintype.card J:ℝ)*(h^2/(12*(m:ℝ))) := by
  classical
  have hn : (fun p => ‖freshAverageNoise m h g p‖^2)=
      ∑ j : J, fun p => freshAverageNoise m h g p j*freshAverageNoise m h g p j := by
    ext p
    simp only [Finset.sum_apply]
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [pow_two]
  rw [hn]
  have hc := condExp_finsetSum (s := Finset.univ) (fun j _ =>
    coordinate_mul_integrable (freshAverageNoise_memLp μ m h g hg) j j)
    (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Ω))
  apply hc.trans
  have hj : ∀ j : J,
      (μ.prod (workerLaw m))[(fun p => freshAverageNoise m h g p j*freshAverageNoise m h g p j) |
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Ω)] =ᵐ[μ.prod (workerLaw m)]
        fun _ => h^2/(12*(m:ℝ)) := by
    intro j
    simpa only [ite_true] using freshAverageNoise_conditional_cross μ m hm h g hg j j
  filter_upwards [Filter.eventually_all.mpr hj] with p hp
  simp only [Finset.sum_apply,hp,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]


/-- Literal worker-averaged quantizer output minus the exact averaged gradient. -/
def workerError (m : ℕ) (h : ℝ) (g : Fin m × J → Ω → ℝ)
    (p : Ω×(Fin m × J → ℝ)) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun j => workerQuantizer m h (fun a => g a p.1) p.2 j-
    (m:ℝ)⁻¹*∑ i : Fin m, g (i,j) p.1)

omit [Fintype J] [MeasurableSpace Ω] in
/-- A nonzero physical quantizer step identifies the literal worker error with
its exact scaled-error representation. -/
theorem workerError_eq (m : ℕ) (h : ℝ) (hh : h≠0) (g : Fin m × J → Ω → ℝ) :
    workerError m h g=freshAverageNoise m h g := by
  funext p
  ext j
  exact (freshAverageNoise_actual m h hh g p j).symm

/-- Literal averaged rounded messages have zero conditional error at every adaptive query. -/
theorem workerError_conditional_mean (m : ℕ) (h : ℝ) (hh : h≠0)
    (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) :
    (μ.prod (workerLaw m))[workerError m h g |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Ω)] =ᵐ[μ.prod (workerLaw m)]
      fun _ => (0 : EuclideanSpace ℝ J) := by
  rw [workerError_eq m h hh]
  exact freshAverageNoise_conditional_mean μ m h g hg

/-- Literal averaged rounded messages have exactly h²/(12m) I covariance. -/
theorem workerError_covariance [DecidableEq J] (m : ℕ) (hm : 0<m) (h : ℝ) (hh : h≠0)
    (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) :
    covarianceMatrix (workerError m h g) (μ.prod (workerLaw m))=
      (h^2/(12*(m:ℝ))) • (1 : Matrix J J ℝ) := by
  rw [workerError_eq m h hh]
  exact freshAverageNoise_covariance μ m hm h g hg

end Fresh


/-- The article's physical quantizer step, for m workers in dimension card J. -/
def workerStep (m : ℕ) (σ : ℝ) : ℝ := σ*Real.sqrt (12*(m:ℝ)/(Fintype.card J:ℝ))

/-- Its exact averaged component variance is sigma squared divided by dimension. -/
theorem workerStep_variance (m : ℕ) (hm : 0<m) (σ : ℝ) :
    workerStep (J := J) m σ^2/(12*(m:ℝ))=σ^2/(Fintype.card J:ℝ) := by
  unfold workerStep
  rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hn : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- For nonzero sigma, positive worker count and positive dimension the literal
rounding formula never divides by a zero quantizer step. -/
theorem workerStep_ne_zero (m : ℕ) (hm : 0<m) (hJ : 0<Fintype.card J) (σ : ℝ) (hσ : σ≠0) :
    workerStep (J := J) m σ≠0 := by
  apply mul_ne_zero hσ
  apply (Real.sqrt_pos.mpr _).ne'
  have hn : (0:ℝ)<m := by exact_mod_cast hm
  have hd : (0:ℝ)<Fintype.card J := by exact_mod_cast hJ
  positivity

/-- With the article's physical step, the actual adaptive averaged quantizer
has exactly the required input-independent covariance sigma²/d I. -/
theorem freshAverageNoise_normalized_covariance [DecidableEq J]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0<m) (σ : ℝ) (g : Fin m × J → Ω → ℝ)
    (hg : ∀ a, Measurable (g a)) :
    covarianceMatrix (freshAverageNoise m (workerStep (J := J) m σ) g) (μ.prod (workerLaw m))=
      (σ^2/(Fintype.card J:ℝ)) • (1 : Matrix J J ℝ) := by
  rw [freshAverageNoise_covariance μ m hm _ g hg,workerStep_variance m hm]


/-- The normalized adaptive component covariance also holds conditionally on the past. -/
theorem freshAverageNoise_normalized_conditional_cross [DecidableEq J]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0<m) (σ : ℝ) (g : Fin m × J → Ω → ℝ)
    (hg : ∀ a, Measurable (g a)) (j k : J) :
    (μ.prod (workerLaw m))[(fun p => freshAverageNoise m (workerStep (J := J) m σ) g p j*
        freshAverageNoise m (workerStep (J := J) m σ) g p k) |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Ω)] =ᵐ[μ.prod (workerLaw m)]
      fun _ => if j=k then σ^2/(Fintype.card J:ℝ) else 0 := by
  simpa only [workerStep_variance m hm] using
    freshAverageNoise_conditional_cross μ m hm (workerStep (J := J) m σ) g hg j k

/-- With the printed h, the actual fresh error has exactly conditional norm budget sigma². -/
theorem freshAverageNoise_normalized_conditional_norm_sq [DecidableEq J]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0<m) (hJ : 0<Fintype.card J) (σ : ℝ)
    (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) :
    (μ.prod (workerLaw m))[(fun p => ‖freshAverageNoise m (workerStep (J := J) m σ) g p‖^2) |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Ω)] =ᵐ[μ.prod (workerLaw m)]
      fun _ => σ^2 := by
  have he := freshAverageNoise_conditional_norm_sq μ m hm (workerStep (J := J) m σ) g hg
  rw [workerStep_variance m hm] at he
  have hd : (Fintype.card J:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  simpa only [mul_div_cancel₀ _ hd] using he


/-- The printed nondegenerate physical quantizer has the article's exact covariance. -/
theorem workerError_normalized_covariance [DecidableEq J]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0<m) (hJ : 0<Fintype.card J) (σ : ℝ) (hσ : σ≠0)
    (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) :
    covarianceMatrix (workerError m (workerStep (J := J) m σ) g) (μ.prod (workerLaw m))=
      (σ^2/(Fintype.card J:ℝ)) • (1 : Matrix J J ℝ) := by
  rw [workerError_eq m _ (workerStep_ne_zero m hm hJ σ hσ)]
  exact freshAverageNoise_normalized_covariance μ m hm σ g hg

/-- Literal fresh rounded-message errors satisfy exactly the required conditional
squared norm budget with the printed step, even at adaptive gradient queries. -/
theorem workerError_normalized_conditional_norm_sq [DecidableEq J]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0<m) (hJ : 0<Fintype.card J) (σ : ℝ) (hσ : σ≠0)
    (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) :
    (μ.prod (workerLaw m))[(fun p => ‖workerError m (workerStep (J := J) m σ) g p‖^2) |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Ω)] =ᵐ[μ.prod (workerLaw m)]
      fun _ => σ^2 := by
  rw [workerError_eq m _ (workerStep_ne_zero m hm hJ σ hσ)]
  exact freshAverageNoise_normalized_conditional_norm_sq μ m hm hJ σ g hg


/-- Every conditional covariance entry of the literal normalized worker quantizer
is sigma²/d times its identity entry. -/
theorem workerError_normalized_conditional_cross [DecidableEq J]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0<m) (hJ : 0<Fintype.card J) (σ : ℝ) (hσ : σ≠0)
    (g : Fin m × J → Ω → ℝ) (hg : ∀ a, Measurable (g a)) (j k : J) :
    (μ.prod (workerLaw m))[(fun p => workerError m (workerStep (J := J) m σ) g p j*
        workerError m (workerStep (J := J) m σ) g p k) |
      MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Ω)] =ᵐ[μ.prod (workerLaw m)]
      fun _ => if j=k then σ^2/(Fintype.card J:ℝ) else 0 := by
  rw [workerError_eq m _ (workerStep_ne_zero m hm hJ σ hσ)]
  exact freshAverageNoise_normalized_conditional_cross μ m hm σ g hg j k

end
end bezout.Probability.Dither
