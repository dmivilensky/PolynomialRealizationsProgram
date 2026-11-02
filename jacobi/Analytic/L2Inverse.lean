import jacobi.Analytic.L2RealCoercivity
import jacobi.Analytic.CoerciveComplexInverse

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The actual continuous-kernel family is norm continuous at the original
real base order. One disk makes its uniform kernel difference smaller
than half the proved original real coercivity gap. The same disk therefore
gives genuine complex L2 inverses with norm at most 2/kappa_star for every
physical interval simultaneously.
Use: closes the separate complex L2 inverse assertion of Appendix E.1 before combining it with the unique analytic continuous transformation kernel.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric MeasureTheory Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] OrderDisk.kernel OrderDisk.kernelTerm OrderDisk.kernelMap
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- One actual complex order disk carries all genuine physical L2 GL inverses with the printed bound 2/kappa_star, using a constant proved for the original real quadratic form.
Use: closes the separate complex L2 inverse assertion of Appendix E.1 before combining it with the unique analytic continuous transformation kernel.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: obtain the original common real coercivity constant and transfer it to complex inputs. Norm continuity of the actual holomorphic kernel gives one closed disk with kernel difference less than kappa_star/2. Every genuine prefix operator difference obeys that bound uniformly in t. The complex Hilbert perturbation theorem then constructs its true inverse and proves the exact printed norm estimate. -/
theorem OrderDisk.L2_inverse_local {a0 : ℝ} (D : OrderDisk a0) (ha0 : -1<a0) :
    ∃ r κ : ℝ,0<r ∧ r<D.radius ∧ 0<κ ∧
      (∀ t∈Ioc (0:ℝ) (1/2),∀ v:Space,
        (∀ᵐ s:Interval,t<(s:ℝ) → v s=0) → κ*‖v‖^2≤quadratic a0 ha0 v) ∧
      (∀ t∈Ioc (0:ℝ) (1/2),
        IsUnit (complexPrefixPositive (D.kernelMap (a0:ℂ)) t) ∧
          ‖Ring.inverse (complexPrefixPositive (D.kernelMap (a0:ℂ)) t)‖≤1/κ) ∧
      ∀ a:ℂ,‖a-(a0:ℂ)‖≤r → ∀ t∈Ioc (0:ℝ) (1/2),
        IsUnit (complexPrefixPositive (D.kernelMap a) t) ∧
          ‖Ring.inverse (complexPrefixPositive (D.kernelMap a) t)‖≤2/κ := by
  -- Neither complex invertibility nor a complex numerical-range gap is among the assumptions.
  obtain ⟨κ,hκ,hreal,hcomplex⟩ := complexPrefix_real_coercive a0 ha0
  have hbase : ‖(a0:ℂ)-(a0:ℂ)‖≤D.radius := by simpa only [sub_self,norm_zero] using D.radius_pos.le
  have hform (t:ℝ) (ht:t∈Ioc (0:ℝ) (1/2)) (v:complexPrefix t) :
      κ*‖v‖^2≤(inner ℂ v (complexPrefixPositive (D.kernelMap (a0:ℂ)) t v)).re := by
    rw [D.kernelMap_real ha0 hbase]
    exact hcomplex t ht v
  have hc : ContinuousAt D.kernelMap (a0:ℂ) := (D.kernelMap_holomorphic.differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_self D.radius_pos))).continuousAt
  have hdiff : ContinuousAt (fun a:ℂ => ‖D.kernelMap a-D.kernelMap (a0:ℂ)‖) (a0:ℂ) :=
    (hc.sub continuousAt_const).norm
  have hs : ∀ᶠ a in 𝓝 (a0:ℂ),‖D.kernelMap a-D.kernelMap (a0:ℂ)‖<κ/2 :=
    hdiff.eventually_lt_const (by simpa only [sub_self,norm_zero] using half_pos hκ)
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hs
  let r : ℝ := min (D.radius/2) (ε/2)
  have hr : 0<r := lt_min (half_pos D.radius_pos) (half_pos hε)
  have hrD : r<D.radius := (min_le_left _ _).trans_lt (by linarith [D.radius_pos])
  refine ⟨r,κ,hr,hrD,hκ,hreal,fun t ht =>
    complex_coercive_inverse _ hκ (hform t ht),fun a ha t ht => ?_⟩
  have hm : a∈ball (a0:ℂ) ε := by
    rw [mem_ball,dist_eq_norm]
    exact ha.trans_lt ((min_le_right _ _).trans_lt (by linarith))
  have hk : ‖D.kernelMap a-D.kernelMap (a0:ℂ)‖<κ/2 := by
    exact hsub hm
  exact complex_coercive_perturbation _ _ hκ (hform t ht)
    ((complexPrefixPositive_dist _ _ t).trans hk.le)

end
end jacobi.Analytic
