import krylov.Convergence.OneGradientTrueMetric
import krylov.Convergence.OneGradientLastEnergyNormalization
import krylov.Convergence.OneGradientSmallSource
import krylov.Convergence.OneGradientFixedInformation

/-!
Article: main_krylov, thm:LB, genuine scalar lower-bound witnesses.
Use: state the conclusion using the actual scalar cubic, its actual local
minimizer, its true positive Hessian, and its true normalized CG error.
Source: exact clipped indistinguishable cubic construction and continuity
of the genuine inverse-root metric and last CG energy. No property of the
method's output, nor regularity of its data-only policy, is presumed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))

/-- A genuine cubic source certificate, with all quantities measured in
its actual Hessian at its actual local minimizer. Article: thm:LB. -/
structure OneGradientCubicLowerWitness
    (method : OneGradientMethod E) (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g a : E) (R budget lower : ℝ) where
  curvature : ℝ
  cubic : ℝ
  minimizer : E
  critical : oneGradientCubicFibreGradient (cgOperator A) g a curvature cubic minimizer=0
  minimum : IsMinOn (oneGradientCubicFibreObjective A g a curvature cubic) {z | ‖z‖≤R} minimizer
  minimizer_size : ‖minimizer‖≤R/2
  positive : (oneGradientCubicTrueHessian A a curvature cubic minimizer).PosDef
  full_reference : referenceAtomCount (oneGradientCubicTrueHessian A a curvature cubic minimizer) positive g=k+1
  tensor_budget : |cubic| *‖cgOperator (metricRoot (oneGradientCubicTrueHessian A a curvature cubic minimizer))⁻¹ a‖^3≤budget
  returned_gradient : lower*‖cgCanonicalError (oneGradientCubicTrueHessian A a curvature cubic minimizer) g k‖^2≤
    ‖cgOperator (metricRoot (oneGradientCubicTrueHessian A a curvature cubic minimizer))⁻¹
      (oneGradientCubicFibreGradient (cgOperator A) g a curvature cubic
        (oneGradientFunctionOutput method (oneGradientCubicFibreGradient (cgOperator A) g a curvature cubic) 0 (k+1)))‖

/-- The physical hidden axis has nonzero inverse-root length.
Article: main_krylov, thm:LB. -/
theorem oneGradient_hidden_axis_inverseRoot_pos
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (a : E) (ha : ‖a‖=1) :
    0<‖cgOperator (metricRoot A)⁻¹ a‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have hh := canonical_search_pairing A hA a a
  change inner ℝ a a=inner ℝ (cgOperator (metricRoot A) a) (cgOperator (metricRoot A)⁻¹ a) at hh
  rw [hz,inner_zero_right,real_inner_self_eq_norm_sq,ha,one_pow] at hh
  norm_num at hh

/-- Every fixed full endpoint admits genuine sources at all sufficiently
small positive forcing scales. The scale is selected before the method
and before its arbitrarily irregular last query. Only the actual scalar
endpoint separation is supplied here; the next leaf derives it from the
original two-completion information argument. Article: thm:LB. -/
theorem oneGradient_endpoint_small_source_witness
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef) (g a : E) (ha : ‖a‖=1)
    (hfull : referenceAtomCount A hA g=k+1)
    (hflag : ∀ v,v∈CG.krylovSpace (cgOperator A) g k ↔ inner ℝ a v=0)
    (Mhat m ρ η : ℝ) (hMhat : 0<Mhat) (hm : 0<m) (hρ : 0≤ρ) (hρ1 : ρ≤1)
    (hη : 0<η) (hη1 : η<1)
    (hbase : ∀ v,m*‖v‖^2≤ inner ℝ v (cgOperator A v)) :
    ∃ R s : ℝ,0<R ∧0<s ∧∀ h : ℝ,0<h → h<s →∀ method : OneGradientMethod E,
      OneGradientSpanRestricted method →
      (ρ*|inner ℝ a (oneGradientQuadraticMinimizer A (h • g))|≤
        |inner ℝ a (oneGradientQuadraticMinimizer A (h • g))-
          inner ℝ a (oneGradientLastQuery method (cgOperator A) (h • g) k)|) →
      ∃ w : OneGradientCubicLowerWitness method A (h • g) a R ((1+η)^3*Mhat)
          ((1-η)/(1+η)^2*(Mhat/2)*ρ),
        ‖oneGradientCubicTrueHessian A a w.curvature w.cubic w.minimizer-A‖≤η*m := by
  let c := ‖cgOperator (metricRoot A)⁻¹ a‖
  let M := Mhat/c^3
  have hc : 0<c := oneGradient_hidden_axis_inverseRoot_pos A hA a ha
  have hM : 0<M := by dsimp only [M];positivity
  let R := m/(8*M)
  have hR : 0<R := by dsimp only [R];positivity
  have hpositive : M*R≤m/4 := by dsimp only [R];field_simp; nlinarith only [hm]
  obtain ⟨ξ₁,hξ₁,hmetric⟩ := oneGradient_dual_metric_relative_neighborhood A hA hη
  obtain ⟨ξ₂,hξ₂,henergy⟩ := oneGradient_last_error_relative_neighborhood A hA g hfull hη
  let ξ := min ξ₁ (min ξ₂ (η*m))
  have hξ : 0<ξ := lt_min hξ₁ (lt_min hξ₂ (mul_pos hη hm))
  let δ := min (m/4) (min (η/(2*c^2)) (ξ/2))
  have hδ : 0<δ := by dsimp only [δ];positivity
  have hδm : δ≤m/2 := by
    have hh : δ≤m/4 := min_le_left _ _
    linarith only [hh,hm]
  have hδB : c^2*δ<η := by
    have hd : δ≤η/(2*c^2) := (min_le_right _ _).trans (min_le_left _ _)
    have hp : 0<2*c^2 := by positivity
    have hb := (le_div_iff₀ hp).mp hd
    nlinarith only [hb,hη]
  have hδξ : δ<ξ := (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hξ))
  obtain ⟨s,hs,hsmall⟩ := oneGradient_small_source_scalars M c m δ η ξ (R/2)
    (inner ℝ a (oneGradientQuadraticMinimizer A g)) ‖g‖ hM hc hm hδ (half_pos hR) hδB hδξ
  refine ⟨R,s,hR,hs,?_⟩
  intro h hh hhsmall method hmeth hsep
  obtain ⟨hy,hforce,hball,hB,hdrift⟩ := hsmall h hh hhsmall
  have hnorm : ‖h • g‖=h*‖g‖ := by rw [norm_smul,Real.norm_of_nonneg hh.le]
  have hycoord : |inner ℝ a (oneGradientQuadraticMinimizer A (h • g))|=
      h*|inner ℝ a (oneGradientQuadraticMinimizer A g)| := by
    rw [oneGradientQuadraticMinimizer_smul,inner_smul_right,abs_mul,abs_of_pos hh]
  have hfullh := oneGradient_full_count_smul A hA g hfull h hh.ne'
  have hflagh : ∀ v,v∈CG.krylovSpace (cgOperator A) (h • g) k ↔ inner ℝ a v=0 := by
    rw [oneGradient_krylovSpace_smul _ _ _ hh.ne'];exact hflag
  have hout := oneGradientCubic_normal_actual_lower method hmeth A hA (h • g) a ha hfullh hflagh
    Mhat δ ρ m R hMhat hδ.le hρ hρ1 hm hbase hδm (by simpa only [hycoord] using hy) hsep
    (by simpa only [hnorm] using hforce) (by rw [hnorm];exact hball.trans (by linarith)) hpositive
  let p := inner ℝ a (oneGradientLastQuery method (cgOperator A) (h • g) k)
  let Mp := oneGradientClippedMagnitude M δ p
  let B := c^2*(M*|inner ℝ a (oneGradientQuadraticMinimizer A (h • g))|+δ)+
    M*c^4/4*|inner ℝ a (oneGradientQuadraticMinimizer A (h • g))| *
      (M*|inner ℝ a (oneGradientQuadraticMinimizer A (h • g))|+2*δ)
  have hBle : B≤η := by dsimp only [B];simpa only [hycoord] using hB
  have hBnn : 0≤B := by dsimp only [B];positivity
  have hMp := oneGradientClippedMagnitude_bounds M δ p hM.le hδ.le
  have hbuild (b t : ℝ) (hb : b∈({-Mp*p/2,Mp*p/2} : Set ℝ)) (ht : t∈({Mp,-Mp} : Set ℝ))
      (hbudget : |t| *c^3≤Mhat)
      (hlower : ((Mhat/2)*ρ*‖cgCanonicalError A (h • g) k‖^2)/(1+B)≤
        ‖cgOperator (metricRoot A)⁻¹ (oneGradientCubicFibreGradient (cgOperator A) (h • g) a b t
          (oneGradientFunctionOutput method (oneGradientCubicFibreGradient (cgOperator A) (h • g) a b t) 0 (k+1)))‖) :
      ∃ w : OneGradientCubicLowerWitness method A (h • g) a R ((1+η)^3*Mhat)
          ((1-η)/(1+η)^2*(Mhat/2)*ρ),
        ‖oneGradientCubicTrueHessian A a w.curvature w.cubic w.minimizer-A‖≤η*m := by
    obtain ⟨x,hx,hmin,hsize,hxdrift,hform⟩ := hout.2.2.2.2 b hb t ht
    let H := oneGradientCubicTrueHessian A a b t x
    have hH : H.PosDef := oneGradientCubicTrueHessian_posDef A hA a b t x (m/4) (by positivity) hform
    have hHA : ‖H-A‖≤ξ := by
      rw [oneGradientCubicTrueHessian_drift]
      exact hxdrift.trans (by simpa only [hnorm] using hdrift)
    have hmetric' := hmetric H hH (hHA.trans (min_le_left _ _))
    have henergy_data := henergy H hH (hHA.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have henergy' := henergy_data.2 h hh
    have htruefull := oneGradient_full_count_smul H hH g henergy_data.1 h hh.ne'
    have htb := oneGradient_rankOne_budget_metric_transfer A H a t Mhat η hMhat.le hη.le hbudget (hmetric' a).2
    have hnormlower := (hmetric' (oneGradientCubicFibreGradient (cgOperator A) (h • g) a b t
      (oneGradientFunctionOutput method (oneGradientCubicFibreGradient (cgOperator A) (h • g) a b t) 0 (k+1)))).1
    have hden : 0<1+B := by positivity
    have heta : 0<1+η := by positivity
    have he : (1-η)/(1+η)^2*(Mhat/2)*ρ*‖cgCanonicalError H (h • g) k‖^2≤
        (1-η)*(((Mhat/2)*ρ*‖cgCanonicalError A (h • g) k‖^2)/(1+B)) := by
      have hE := henergy'.2
      calc
        _ ≤ ((1-η)/(1+η)^2*(Mhat/2)*ρ)*((1+η)*‖cgCanonicalError A (h • g) k‖^2) :=
          mul_le_mul_of_nonneg_left hE (by positivity)
        _ = ((1-η)*(Mhat/2)*ρ*‖cgCanonicalError A (h • g) k‖^2)/(1+η) := by
          field_simp
        _ ≤ ((1-η)*(Mhat/2)*ρ*‖cgCanonicalError A (h • g) k‖^2)/(1+B) :=
          div_le_div_of_nonneg_left (by positivity) hden (by linarith only [hBle])
        _ = _ := by ring
    refine ⟨⟨b,t,x,hx,hmin,hsize.trans (by simpa only [hnorm] using hball),hH,htruefull,htb,he.trans ((mul_le_mul_of_nonneg_left hlower (by linarith)).trans hnormlower)⟩,?_⟩
    exact hHA.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hMpnn : 0≤Mp := hMp.1
  have houtbudget : Mp*c^3≤Mhat := hout.1
  have hlo := hout.2.2.2.1
  change _≤max _ _ at hlo
  rcases le_max_iff.mp hlo with hp|hm
  · apply hbuild (-Mp*p/2) Mp (by simp) (by simp) (by simpa only [abs_of_nonneg hMpnn] using houtbudget) hp
  · apply hbuild (Mp*p/2) (-Mp) (by simp) (by simp) (by simpa only [abs_neg,abs_of_nonneg hMpnn] using houtbudget) hm

end
end krylov.Convergence
