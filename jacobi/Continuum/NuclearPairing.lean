import chebyshev2.Continuum.TraceClassFeature
import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
Article: jacobi, Appendix D.1 (trace-class feature operators).
Bounded operators can be paired with signed feature-density operators in
the actual nuclear-norm Banach space. Their traces are the expected feature
integrals, independently of the chosen Hilbert basis. This supplies the
Fredholm gradient identity without a formal trace notation or an assumed
trace-ideal multiplication rule.
Source: rank-one nuclear norms and continuity of the nuclear trace.
Use: integrates bounded-operator compositions with signed feature densities.
-/
namespace jacobi.Continuum
noncomputable section
open MeasureTheory Real Filter chebyshev2.Continuum
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The genuine rank-one operator as an element of the nuclear-norm Banach space.
Use: integrates bounded-operator compositions with signed feature densities.
Article: jacobi, Appendix D.1 (trace-class feature operators).
-/
def nuclearRankOne (u v : FeatureSpace) : TraceClassOperator FeatureSpace :=
  ⟨InnerProductSpace.rankOne ℝ u v,rankOne_isTraceClass u v⟩

/-- The rank-one nuclear norm is exactly the product of the vector norms.
Use: bounds all composed feature integrands by a single multiple of the L1 density.
Article: jacobi, Appendix D.1 (trace-class feature operators).
Proof: use the previously proved exact nuclear norm of a rank-one operator. -/
theorem nuclearRankOne_norm (u v : FeatureSpace) : ‖nuclearRankOne u v‖=‖u‖*‖v‖ := by
  rw [TraceClassOperator.norm_def]
  change (nuclearNorm (InnerProductSpace.rankOne ℝ u v)).toReal=_
  rw [nuclearNorm_rankOne,ENNReal.toReal_ofReal (by positivity)]

/-- Rank-one formation is bounded bilinear in the genuine nuclear topology.
Use: proves strong measurability of the varying composed feature integrand.
Article: jacobi, Appendix D.1 (trace-class feature operators).
Proof: rank-one linearity is checked on the underlying operators; its exact
nuclear norm supplies the bilinear bound with constant one. -/
theorem nuclearRankOne_bilinear :
    IsBoundedBilinearMap ℝ (fun p : FeatureSpace × FeatureSpace => nuclearRankOne p.1 p.2) where
  -- The inclusion is injective; all four algebraic identities can be verified as actual operators.
  add_left u v w := by
    -- Equality in nuclear space follows from equality of the underlying bounded rank-one operators.
    apply TraceClassOperator.ext
    simp [nuclearRankOne,TraceClassOperator.val_add,map_add]
  smul_left c u v := by
    apply TraceClassOperator.ext
    simp [nuclearRankOne,TraceClassOperator.val_smul]
  add_right u v w := by
    apply TraceClassOperator.ext
    simp [nuclearRankOne,TraceClassOperator.val_add,map_add]
  smul_right c u v := by
    apply TraceClassOperator.ext
    simp [nuclearRankOne,TraceClassOperator.val_smul]
  bound := ⟨1,by norm_num,fun u v => by simp only [nuclearRankOne_norm,one_mul,le_refl]⟩

/-- Signed density times a bounded-operator rank-one feature is nuclear-Bochner integrable.
Use: all trace-gradient integrals below concern actual trace-class operators.
Article: jacobi, Appendix D.1 (trace-class feature operators).
Proof: continuity of nuclear rank-one formation gives measurability, while
its norm is bounded by norm(A)*abs(delta), an integrable scalar majorant. -/
theorem composedFeature_integrable (A : FeatureSpace →L[ℝ] FeatureSpace)
    {d : ℝ → ℝ} (hd : Integrable d) :
    Integrable (fun x => d x • nuclearRankOne (A (feature x)) (feature x)) := by
  -- The estimate is made in nuclear norm, so commuting the trace with this integral is justified.
  apply (hd.abs.const_mul ‖A‖).mono'
  · exact hd.aestronglyMeasurable.smul
      (nuclearRankOne_bilinear.continuous.comp
        ((A.continuous.comp feature_continuous).prodMk feature_continuous)).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      rw [norm_smul,Real.norm_eq_abs,nuclearRankOne_norm,feature_norm,mul_one]
      have hb : ‖A (feature x)‖≤‖A‖ := by simpa only [feature_norm,mul_one] using A.le_opNorm (feature x)
      nlinarith [abs_nonneg (d x)]

/-- The actual nuclear operator formed by left-composing A with a signed feature density.
Use: gives a bona fide trace-class value for the Fredholm derivative pairing.
Article: jacobi, Appendix D.1 (trace-class feature operators).
-/
def composedDensity (A : FeatureSpace →L[ℝ] FeatureSpace) (d : ℝ → ℝ) :
    TraceClassOperator FeatureSpace := ∫ x,d x • nuclearRankOne (A (feature x)) (feature x)

/-- The nuclear construction is exactly composition of the original bounded and density operators.
Use: excludes replacing the operator trace by an independently defined scalar pairing.
Article: jacobi, Appendix D.1 (trace-class feature operators).
Proof: pass the nuclear integral through its continuous inclusion, evaluate
at an arbitrary vector, and commute A with the signed density's Bochner integral. -/
theorem composedDensity_val (A : FeatureSpace →L[ℝ] FeatureSpace)
    {d : ℝ → ℝ} (hd : Integrable d) :
    (composedDensity A d).val=A ∘L densityOperator d := by
  -- Both sides are identified as bounded operators before any trace is taken.
  have hi := composedFeature_integrable A hd
  have he := (TraceClassOperator.toOperator FeatureSpace).integral_comp_comm hi
  change (∫ x,d x • InnerProductSpace.rankOne ℝ (A (feature x)) (feature x))=
    (composedDensity A d).val at he
  rw [← he]
  have hc := (ContinuousLinearMap.compL ℝ FeatureSpace FeatureSpace FeatureSpace A).integral_comp_comm
    (densityOperator_integrable hd)
  change (∫ x,A ∘L (d x • featureProjection x))=A ∘L densityOperator d at hc
  rw [← hc]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change d x • InnerProductSpace.rankOne ℝ (A (feature x)) (feature x)=A ∘L (d x • featureProjection x)
    rw [ContinuousLinearMap.comp_smul,featureProjection,InnerProductSpace.comp_rankOne]

/-- The trace of the actual composition is the signed feature quadratic integral.
Use: specializes to s*(2g-1), the genuine Fredholm first-variation gradient.
Article: jacobi, Appendix D.1 (trace-class feature operators).
Proof: the continuous nuclear trace commutes with the proved Bochner integral;
the trace of each genuine rank-one term is its vector inner product. -/
theorem composedDensity_trace {ι : Type*} (b : HilbertBasis ι ℝ FeatureSpace)
    (A : FeatureSpace →L[ℝ] FeatureSpace) {d : ℝ → ℝ} (hd : Integrable d) :
    TraceClassOperator.trace b (composedDensity A d)=
      ∫ x,d x*inner ℝ (A (feature x)) (feature x) := by
  -- Nuclear integrability is established before the trace and integral are interchanged.
  rw [composedDensity,← (TraceClassOperator.trace b).integral_comp_comm (composedFeature_integrable A hd)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change TraceClassOperator.trace b (d x • nuclearRankOne (A (feature x)) (feature x))=_
    rw [map_smul]
    change d x*TraceClassOperator.trace b
      ⟨InnerProductSpace.rankOne ℝ (A (feature x)) (feature x),_⟩=_
    rw [TraceClassOperator.trace_rankOne]

end
end jacobi.Continuum
