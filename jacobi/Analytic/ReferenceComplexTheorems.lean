import jacobi.Analytic.ReferenceJointHolomorphy
import jacobi.Analytic.ReferenceSharpEnergy
import jacobi.Analytic.ReferenceNormIntegral

/-!
Article: jacobi, Lemma C.1.
The original complex reference functions satisfy joint holomorphy,
the printed compact-order sharp derivative estimate and the exact
Gegenbauer and integral norming identities. The constants apply to the
actual full-index spectral objects and preserve the original normalization.
Use: completes fnC(a) for nonreal orders and identifies the same functions in the actual bilinear norm integral.
-/
namespace jacobi.ComplexReference
noncomputable section
open _root_.Complex Set Metric Filter MeasureTheory
open jacobi.Reference (Interval)
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The genuine complex reference function on its original reference spectrum is exactly the normalized Gegenbauer expression throughout the physical interior.
Use: completes fnC(a) for nonreal orders and identifies the same functions in the actual bilinear norm integral.
Article: jacobi, Lemma C.1.
Proof: the actual reference eigenfunction is the finite normalized Jacobi polynomial times the original sine prefactor. The proved Gegenbauer/Jacobi normalization identity gives the literal polynomial quotient; positive physical bases split its complex sine and pi powers exactly. -/
theorem reference_gegenbauer {a:ℂ} (ha:0<(gamma a).re) (k:ℕ) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) :
    solution a (jacobi.Hankel.frequencyReference a k) t=
      (Real.pi:ℂ)^(-gamma a)*(Real.sin (Real.pi*t):ℂ)^gamma a*
        (jacobi.Jacobi.gegenbauer (gamma a) k (Real.cos (Real.pi*t):ℂ)/
          jacobi.Jacobi.gegenbauer (gamma a) k 1) := by
  -- The underlying finite polynomial equality is valid at every admissible complex order.
  rw [jacobi.Jacobi.gegenbauer_normalized ha]
  have hpoly : referenceEigenMap a k ⟨t,⟨ht.1.le,ht.2.le⟩⟩=
      weight a t* jacobi.Jacobi.normalized (gamma a-1/2) (gamma a-1/2) k (Real.cos (Real.pi*t):ℂ) := by
    rw [referenceEigenMap,ContinuousMap.mul_apply,weightUnitMap_apply ha,jacobi.Jacobi.normalized_eq_sum]
    simp only [referencePolynomialMap,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
      smul_eq_mul,referenceCoordinatePower,ContinuousMap.coe_mk]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    congr 2
    push_cast
    rfl
  rw [show solution a (jacobi.Hankel.frequencyReference a k) t=
    referenceEigenMap a k ⟨t,⟨ht.1.le,ht.2.le⟩⟩ from
      solution_at_reference_complex ha k ⟨t,⟨ht.1.le,ht.2.le⟩⟩,hpoly]
  unfold weight
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (jacobi.Reference.sine_pos ht).le Real.pi_pos.le,
    Complex.cpow_neg]
  ring

/-- The actual reference amplitude and exact sharp energy derivative estimates hold uniformly on every compact admissible complex-order set.
Use: completes the printed compact-parameter form of fboundC(b), with the exact spatial and reciprocal-frequency gains.
Article: jacobi, Lemma C.1.
Proof: compactness bounds the genuine exponent norm. Its positive real part gives a common denominator margin of one half. Apply the proved uniform amplitude and sharp derivative theorems and enlarge their two actual constants to one. The nonzero-frequency formulation of the amplitude minimum leaves its removable zero-frequency value to the already proved endpoint envelope. -/
theorem reference_compact_strip_bounds {K:Set ℂ} (hK:IsCompact K)
    (hpos:∀ a∈K,0<(gamma a).re) (b:ℝ) :
    ∃ C:ℝ,0<C ∧ ∀ a∈K,
      (∀ omega:ℂ,omega≠0 → |omega.im|≤b → ∀ t∈Icc (0:ℝ) (1/2),
        ‖solution a (jacobi.Hankel.besselCoefficient a+omega^2) t‖≤
          C*min (t^(gamma a).re) (‖omega‖^(-(gamma a).re))) ∧
      (∀ omega:ℂ,1≤‖omega‖ → |omega.im|≤b → ∀ t∈Icc (0:ℝ) (1/2),
        ‖deriv (fun z => solution a z t) (jacobi.Hankel.besselCoefficient a+omega^2)‖≤
          C*t/‖omega‖*min (t^(gamma a).re) (‖omega‖^(-(gamma a).re))) := by
  -- Compactness fixes the order constants before frequency and either spatial coordinate are chosen.
  have hg : Continuous gamma := by unfold gamma; fun_prop
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  let G : ℝ := |B|+1
  have hG : 0<G := by dsimp [G]; positivity
  obtain ⟨A,hA,hamp⟩ := wave_strip_bound hG (by norm_num : (0:ℝ)<1/2) b
  obtain ⟨D,hD,hder⟩ := sharp_energy_derivative_uniform hG (by norm_num : (0:ℝ)<1/2) b
  refine ⟨A+D,by positivity,fun a ha => ?_⟩
  have hag := hpos a ha
  have haG : ‖gamma a‖≤G := (hB a ha).trans (by dsimp [G]; linarith [le_abs_self B])
  have haδ : (1/2:ℝ)≤(gamma a+1/2).re := by norm_num; linarith
  constructor
  · intro omega hne him t ht
    rw [solution_eq_wave a (omega := omega) (by ring) t]
    exact (hamp a omega hag haG haδ hne him t ht).trans
      (mul_le_mul_of_nonneg_right (by linarith : A≤A+D)
        (le_min (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (norm_nonneg _) _)))
  · intro omega hR him t ht
    have hh := hder a omega hag haG haδ hR him t ht
    apply hh.trans
    have hmin : 0≤min (t^(gamma a).re) (‖omega‖^(-(gamma a).re)) :=
      le_min (Real.rpow_nonneg ht.1 _) (Real.rpow_nonneg (norm_nonneg _) _)
    apply mul_le_mul_of_nonneg_right ?_ hmin
    apply div_le_div_of_nonneg_right ?_ (norm_nonneg omega)
    exact mul_le_mul_of_nonneg_right (by linarith : D≤A+D) ht.1

end
end jacobi.ComplexReference
