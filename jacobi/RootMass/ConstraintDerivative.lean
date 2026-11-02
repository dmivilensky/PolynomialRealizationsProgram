import jacobi.RootMass.Constraint
import jacobi.RootMass.NodeGeometry
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
Article: jacobi, Theorem D.8.
Differentiation uses the original nonsingular K quadrature, so no endpoint
singularity is introduced. Its derivative is jointly continuous even at u=1;
compact local domination proves genuine differentiation under the integral.
The certified Q derivative gives strict positivity on the open unit interval.
Source: smooth rational weights and dominated parametric integration in mathlib.
Use: its genuine derivative is continuous along the full inverse curve, including u=1.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The actual nonsingular spectral weight is smooth at every true state value.
Use: its genuine derivative is continuous along the full inverse curve, including u=1.
Article: jacobi, Theorem D.8.
Proof: the rational denominator is nonzero since n>=1 and q(n)>0. -/
theorem K_contDiffAt {a n : ℝ} (ha : -2*sqrt 3<a) (hn : 1≤n) : ContDiffAt ℝ ∞ (K a) n := by
  have hP : ContDiffAt ℝ ∞ (p a) n := by unfold p; fun_prop
  have hQ : ContDiffAt ℝ ∞ (q a) n := by unfold q; fun_prop
  exact (hP.pow 3).div ((contDiffAt_id.pow 2).mul hQ)
    (mul_ne_zero (pow_ne_zero 2 (zero_lt_one.trans_le hn).ne') (q_pos ha hn).ne')

/-- The actual inverse-coordinate state has its classical parameter derivative even at both integration endpoints.
Use: differentiates the nonsingular integrand without discarding the endpoint u=1 in the continuity argument.
Article: jacobi, Theorem D.8.
Proof: for u<1 compose the actual inverse derivative with its positive linear argument; at u=1 the state is the literal constant one. -/
theorem node_parameter_hasDerivAt {a y u : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivAt (fun t => node a ha t u) ((1-u^2)/psiSlope a (node a ha y u)) y := by
  -- Treat the constant endpoint u=1 separately before using the actual inverse derivative.
  by_cases he : u=1
  · subst u
    simpa only [node_one,one_pow,sub_self,zero_div] using hasDerivAt_const y (1:ℝ)
  · have hr : 0<1-u^2 := by nlinarith [hu.1,hu.2,lt_of_le_of_ne hu.2 he]
    convert (inverse_hasDerivAt ha (mul_pos hy hr)).comp y
      ((hasDerivAt_id y).mul_const (1-u^2)) using 1
    · rfl
    · dsimp only [id_eq,node]
      ring

/-- The genuine nonsingular derivative integrand of the actual constraint quadrature.
Use: its continuous unit integral is the classical derivative of Ghat.
Article: jacobi, Theorem D.8.
-/
def constraintSlopeIntegrand (a : ℝ) (ha : -2*sqrt 3<a) (y u : ℝ) : ℝ :=
  8*y*K a (node a ha y u)+4*y^2*deriv (K a) (node a ha y u)*
    ((1-u^2)/psiSlope a (node a ha y u))

/-- The true derivative integrand is jointly continuous, including u=1 and every finite parameter endpoint.
Use: gives a genuine compact dominating constant and continuity of the integrated derivative.
Article: jacobi, Theorem D.8.
Proof: K and its actual derivative are smooth at every inverse state;
psi' is positive there, so every denominator is nonzero. -/
theorem constraintSlopeIntegrand_continuous (a : ℝ) (ha : -2*sqrt 3<a) :
    Continuous (fun z : ℝ × ℝ => constraintSlopeIntegrand a ha z.1 z.2) := by
  -- The original nonsingular representation avoids division by 1-u².
  have hn := node_continuous a ha
  have hKd : Continuous (fun z : ℝ × ℝ => deriv (K a) (node a ha z.1 z.2)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((K_contDiffAt (n := node a ha z.1 z.2) ha (inverse_ge_one a ha _)).derivWithin (m := 0) (by simp)).continuousAt.comp (f := fun z : ℝ × ℝ => node a ha z.1 z.2) hn.continuousAt
  have hpsi : Continuous (fun z : ℝ × ℝ => psiSlope a (node a ha z.1 z.2)) := by
    unfold psiSlope p q
    fun_prop (disch := intro z; have h := (p_bounds ha (inverse_ge_one a ha (z.1*(1-z.2^2)))); exact pow_ne_zero 3 (h.1.trans_le h.2.1).ne')
  have hi : Continuous (fun z : ℝ × ℝ => (1-z.2^2)/psiSlope a (node a ha z.1 z.2)) :=
    (continuous_const.sub (continuous_snd.pow 2)).div hpsi (fun _ => (psiSlope_pos ha (inverse_ge_one a ha _)).ne')
  exact ((continuous_const.mul continuous_fst).mul (K_node_continuous a ha)).add
    (((continuous_const.mul (continuous_fst.pow 2)).mul hKd).mul hi)

/-- The actual nonsingular constraint integrand has the stated classical parameter derivative.
Use: dominated differentiation computes the true Ghat derivative, rather than a merely formal expression.
Article: jacobi, Theorem D.8.
Proof: apply the product and chain rules to the genuine inverse derivative and smooth actual rational weight. -/
theorem constraint_integrand_hasDerivAt {a y u : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivAt (fun t => 4*t^2*K a (node a ha t u)) (constraintSlopeIntegrand a ha y u) y := by
  have hk := (K_contDiffAt (n := node a ha y u) ha (inverse_ge_one a ha _)).differentiableAt (by simp)
  convert ((((hasDerivAt_id y).pow 2).const_mul 4).mul
    (hk.hasDerivAt.comp y (node_parameter_hasDerivAt ha hy hu))) using 1
  · rfl
  · unfold constraintSlopeIntegrand
    dsimp only [Function.comp_def,Pi.pow_apply,id_eq]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    ring

/-- The actual spectral constraint has a genuine classical derivative given by its continuous nonsingular derivative integral.
Use: proves C1 regularity of Ghat and allows the certified positive derivative comparison.
Article: jacobi, Theorem D.8.
Proof: bound the jointly continuous derivative integrand on a compact
parameter neighborhood times [0,1]. This constant is integrable on the unit
interval. The actual parametric differentiation theorem then applies. -/
theorem Ghat_hasDerivAt {a y : ℝ} (ha : -2*sqrt 3<a) (hy : 0<y) :
    HasDerivAt (Ghat a ha) (∫ u in Icc (0:ℝ) 1,constraintSlopeIntegrand a ha y u) y := by
  -- All domination bounds are proved on an actual compact parameter neighborhood.
  let s := Icc (y/2) (y+1)
  have hs : s∈𝓝 y := Icc_mem_nhds (by linarith) (by linarith)
  have hc := constraintSlopeIntegrand_continuous a ha
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod (isCompact_Icc : IsCompact (Icc (0:ℝ) 1))).exists_bound_of_continuousOn
    (hc.continuousOn (s := s ×ˢ Icc (0:ℝ) 1))
  have hF : Continuous (fun z : ℝ × ℝ => 4*z.1^2*K a (node a ha z.1 z.2)) :=
    (continuous_const.mul (continuous_fst.pow 2)).mul (K_node_continuous a ha)
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc (0:ℝ) 1)) (s := s)
    (F := fun t u => 4*t^2*K a (node a ha t u)) (F' := constraintSlopeIntegrand a ha)
    (bound := fun _ => B) hs
    (Eventually.of_forall fun t => (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ((hF.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact isCompact_Icc)
    ((hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu; intro t ht; exact hB (t,u) ⟨ht,hu⟩)
    (integrableOn_const isCompact_Icc.measure_ne_top)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      intro t ht
      exact constraint_integrand_hasDerivAt ha (by have ht' : y/2≤t := ht.1; linarith) hu)
  have he : (fun t => ∫ u in Icc (0:ℝ) 1,4*t^2*K a (node a ha t u))=Ghat a ha := by
    funext t
    rw [integral_const_mul,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
    rfl
  rw [he] at hh
  exact hh.2

end
end jacobi.RootMass
