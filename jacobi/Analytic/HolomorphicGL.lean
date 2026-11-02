import jacobi.Analytic.L2Inverse
import jacobi.Analytic.ComplexCutoffFormula
import jacobi.Analytic.ProfileEnergyNormalization

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
One common genuine complex order disk supports both the physical L2
inverse estimate and the unique bounded analytic transformation kernel.
The same disk carries the actual normally convergent profile and its
holomorphic energy. All constants and inverses are derived from the
original real data; no continuation or invertibility premises remain.
Appendix E.1 holds on the larger OrderDisk already constructed
in NormingProducts and KernelHolomorphy, hence on this same subdisk.
Use: synchronizes the physical Hilbert inverse theorem with the continuous-kernel analytic construction and subsequent profile series.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric MeasureTheory Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A single disk carries the actual square GL inverse solution and all physical complex L2 inverses with the original real coercivity constant.
Use: synchronizes the physical Hilbert inverse theorem with the continuous-kernel analytic construction and subsequent profile series.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: intersect the two already proved genuine closed inverse neighborhoods. Keep the real coercivity constant from the L2 theorem and the continuous-kernel bound from the square inverse theorem. Restriction to the smaller disk preserves both conclusions. -/
theorem OrderDisk.GL_local_complete {a0 : ℝ} (D : OrderDisk a0) (ha0 : -1<a0) :
    ∃ r κ B : ℝ,0<r ∧ r<D.radius ∧ 0<κ ∧ 0<B ∧
      (∀ t∈Ioc (0:ℝ) (1/2),∀ v:Space,
        (∀ᵐ s:Interval,t<(s:ℝ) → v s=0) → κ*‖v‖^2≤quadratic a0 ha0 v) ∧
      ∀ a:ℂ,‖a-(a0:ℂ)‖≤r →
        IsUnit (D.GLoperator a) ∧ ‖D.GLsolution a‖≤B ∧
          ∀ t∈Ioc (0:ℝ) (1/2),IsUnit (complexPrefixPositive (D.kernelMap a) t) ∧
            ‖Ring.inverse (complexPrefixPositive (D.kernelMap a) t)‖≤2/κ := by
  -- Intersect actual neighborhoods of the same original spectral disk and the same real base order.
  obtain ⟨rK,B,hrK,hrKD,hB,hK,_⟩ := D.GLsolution_local ha0
  obtain ⟨rL,κ,hrL,hrLD,hκ,hreal,_,hL⟩ := D.L2_inverse_local ha0
  refine ⟨min rK rL,κ,B,lt_min hrK hrL,(min_le_left _ _).trans_lt hrKD,hκ,hB,hreal,?_⟩
  intro a ha
  obtain ⟨hu,hb⟩ := hK a (ha.trans (min_le_left _ _))
  exact ⟨hu,hb,hL a (ha.trans (min_le_right _ _))⟩

/-- The original article data admit the full analytic GL assertion on one common disk: every genuine complex L2 interval inverse has norm at most 2/kappa_star, and the original continuous triangular kernel exists uniquely, is uniformly bounded, holomorphic, and has the exact original real restriction.
Use: closes all of Appendix E.1, including its actual Hilbert operator assertion and arbitrary continuous candidate uniqueness.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: obtain the genuine numbered spectral disk and its common completed GL neighborhood. The physical inverse statement is already proved there with an original real coercivity constant. The actual square inverse supplies the literal triangular equation, full uniqueness, uniform norm bound and pointwise holomorphy. Its original real identification is the previously proved exact kernel equality. -/
theorem analytic_GL {a0 : ℝ} (ha0 : -1<a0) :
    ∃ D : OrderDisk a0,∃ r κ C : ℝ,0<r ∧ r<D.radius ∧ 0<κ ∧ 0<C ∧
      (∀ t∈Ioc (0:ℝ) (1/2),∀ v:Space,
        (∀ᵐ s:Interval,t<(s:ℝ) → v s=0) → κ*‖v‖^2≤quadratic a0 ha0 v) ∧
      (∀ a:ℂ,‖a-(a0:ℂ)‖≤r →
        (∀ t∈Ioc (0:ℝ) (1/2),IsUnit (complexPrefixPositive (D.kernelMap a) t) ∧
          ‖Ring.inverse (complexPrefixPositive (D.kernelMap a) t)‖≤2/κ) ∧
        (∃! K : C(Triangle,ℂ),D.SatisfiesGL a K) ∧
          ∀ p:Triangle,‖D.GLtriangle a p‖≤C) ∧
      (∀ p:Triangle,DifferentiableOn ℂ (fun a => D.GLtriangle a p) (ball (a0:ℂ) r)) ∧
      (∀ b:ℝ,∀ hb:-1<b,‖(b:ℂ)-(a0:ℂ)‖≤r → ∀ p:Triangle,
        D.GLtriangle (b:ℂ) p=(transformationKernel b hb p.val.1 p.val.2:ℂ)) := by
  -- The sole input is admissibility of the original real order.
  obtain ⟨D⟩ := orderDisk_nonempty ha0
  obtain ⟨r,κ,C,hr,hrD,hκ,hC,hreal,hdata⟩ := D.GL_local_complete ha0
  have hunit : ∀ a∈ball (a0:ℂ) r,IsUnit (D.GLoperator a) :=
    fun a ha => (hdata a (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ha))).1
  refine ⟨D,r,κ,C,hr,hrD,hκ,hC,hreal,?_,D.GLtriangle_holomorphic hrD.le hunit,?_⟩
  · intro a ha
    obtain ⟨hu,hbound,hL⟩ := hdata a ha
    exact ⟨hL,⟨D.GLtriangle a,D.GLtriangle_satisfiesGL hu,D.GLtriangle_unique hu⟩,
      fun p => ((D.GLsolution a).norm_coe_le_norm p.val).trans hbound⟩
  · intro b hb hbd p
    exact D.GLtriangle_real hb (hbd.trans hrD.le) p

/-- The complete actual GL inverse and the original analytic profile-and-energy construction hold on the very same complex disk.
Use: removes any possible mismatch between the physical Hilbert inverse neighborhood in holo(c) and the transformed spectral series in holo(d).
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: use the proved common GL neighborhood, with its actual square solution bound. The original transformed-wave holomorphy, profile normal majorant and Banach-valued sum then apply on that same disk. The true squared-profile integral is holomorphic there and has the original real value. -/
theorem analytic_GL_profile_energy {a0 : ℝ} (ha0 : -1<a0) :
    ∃ D : OrderDisk a0,∃ r κ C : ℝ,0<r ∧ r<D.radius ∧ 0<κ ∧ 0<C ∧
      (∀ a:ℂ,‖a-(a0:ℂ)‖≤r →
        (∀ t∈Ioc (0:ℝ) (1/2),IsUnit (complexPrefixPositive (D.kernelMap a) t) ∧
          ‖Ring.inverse (complexPrefixPositive (D.kernelMap a) t)‖≤2/κ) ∧
        (∃! K:C(Triangle,ℂ),D.SatisfiesGL a K) ∧
          ‖D.GLsolution a‖≤C ∧ ‖D.profileMap a‖≤C) ∧
      DifferentiableOn ℂ D.GLsolution (ball (a0:ℂ) r) ∧
      (∀ k,DifferentiableOn ℂ (D.transformedMap k) (ball (a0:ℂ) r)) ∧
      TendstoUniformlyOn (fun N:ℕ => fun a:ℂ => ∑ k∈Finset.range N,D.profileTerm k a)
        D.profileMap atTop (closedBall (a0:ℂ) r) ∧
      (∀ a:ℂ,‖a-(a0:ℂ)‖≤r →
        D.persymmetricEnergy a=2*(∫ t:Interval in prefixSet (1/2),(D.profileMap a t)^2)) ∧
      DifferentiableOn ℂ D.profileMap (ball (a0:ℂ) r) ∧
      DifferentiableOn ℂ D.persymmetricEnergy (ball (a0:ℂ) r) ∧
      (∀ b:ℝ,∀ hb:-1<b,‖(b:ℂ)-(a0:ℂ)‖≤r →
        D.GLsolution (b:ℂ)=continuousOfReal (realTransformationMap b hb) ∧
        D.profileMap (b:ℂ)=continuousOfReal (persymmetricProfile b hb) ∧
        D.persymmetricEnergy (b:ℂ)=(persymmetricConstant b hb:ℂ)) := by
  -- All families use the same original spectrum, kernel, physical measure and common disk.
  obtain ⟨D⟩ := orderDisk_nonempty ha0
  obtain ⟨r,κ,B,hr,hrD,hκ,hB,_,hdata⟩ := D.GL_local_complete ha0
  have hbound := fun a ha => (hdata a ha).2.1
  have hunit : ∀ a∈ball (a0:ℂ) r,IsUnit (D.GLoperator a) :=
    fun a ha => (hdata a (le_of_lt (by simpa only [mem_ball,dist_eq_norm] using ha))).1
  obtain ⟨P,hP,hφ⟩ := D.profileMap_bound hrD.le hB hbound
  refine ⟨D,r,κ,B+P,hr,hrD,hκ,by positivity,?_,D.GLsolution_holomorphic hrD.le hunit,
    D.transformedMap_holomorphic hrD.le hunit,D.profileMap_uniform hrD.le hB hbound,
    fun _ ha => D.persymmetricEnergy_half hrD.le hB hbound ha,
    D.profileMap_holomorphic hrD.le hB hbound hunit,
    D.persymmetricEnergy_holomorphic hrD.le hB hbound hunit,?_⟩
  · intro a ha
    obtain ⟨hu,hb,hL⟩ := hdata a ha
    exact ⟨hL,⟨D.GLtriangle a,D.GLtriangle_satisfiesGL hu,D.GLtriangle_unique hu⟩,
      hb.trans (by linarith), (hφ a ha).trans (by linarith)⟩
  · intro b hb hbd
    exact ⟨D.GLsolution_real hb (hbd.trans hrD.le),D.profileMap_real hrD.le hB hbound hb hbd,
      D.persymmetricEnergy_real hrD.le hB hbound hb hbd⟩

end
end jacobi.Analytic
