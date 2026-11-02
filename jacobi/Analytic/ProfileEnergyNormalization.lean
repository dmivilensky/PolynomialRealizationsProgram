import jacobi.Analytic.PersymmetricEnergy

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Reflection holds for the continued complex profile itself. Its genuine
whole-interval squared integral is therefore exactly twice its physical
half-interval integral, also at nonreal orders. This identifies the
analytic energy with the literal complex formula printed in the article.
Use: identifies the full continued profile and its energy with the article's reflected half-domain formulas.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric MeasureTheory Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every continued original profile term has the prescribed physical reflection symmetry, including at complex order.
Use: identifies the full continued profile and its energy with the article's reflected half-domain formulas.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the physical folding coordinate is unchanged by reflection, so the literal squared transformed-wave term is unchanged. -/
theorem OrderDisk.profileTerm_reflection {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) (a : ℂ) (t : Interval) :
    D.profileTerm k a (physicalReflection t)=D.profileTerm k a t := by
  change _*((D.transformedMap k a (physicalFold (physicalReflection t)))^2)=
    _*((D.transformedMap k a (physicalFold t))^2)
  rw [physicalFold_reflection]

/-- The actual normally convergent continued complex profile has precisely the original reflection symmetry.
Use: converts its genuine energy integral to the printed twice-half-domain formula without relying only on real-order equality.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: commute each genuine point evaluation with the proved norm-summable original profile series and use reflection of every actual term. -/
theorem OrderDisk.profileMap_reflection {a0 r B : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hB : 0<B) (hbound : ∀ a:ℂ,‖a-(a0:ℂ)‖≤r → ‖D.GLsolution a‖≤B)
    {a : ℂ} (ha : ‖a-(a0:ℂ)‖≤r) (t : Interval) :
    D.profileMap a (physicalReflection t)=D.profileMap a t := by
  rw [D.profileMap_apply hrD hB hbound ha,D.profileMap_apply hrD hB hbound ha]
  exact tsum_congr (fun k => D.profileTerm_reflection k a t)

/-- A genuinely continuous reflected complex function has twice its physical prefix integral.
Use: fixes the exact factor two in the original continued squared-profile energy.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Source: reflection substitution for the Bochner interval integral.
Proof: extend the continuous function to the real line by interval projection. The genuine subtype integral is its original unit interval integral. Split at the midpoint and reflect the right half onto the left; both genuine half integrals are equal. -/
theorem reflected_integral_half (f : C(Interval,ℂ))
    (hf : ∀ t:Interval,f (physicalReflection t)=f t) :
    (∫ t:Interval,f t)=2*(∫ t:Interval in prefixSet (1/2),f t) := by
  -- Projection extends only the unused exterior coordinates and fixes every original integration point.
  let G : ℝ → ℂ := fun t => f (Set.projIcc (0:ℝ) 1 (by norm_num) t)
  have hG : Continuous G := f.continuous.comp continuous_projIcc
  have he (t:Interval) : G (t:ℝ)=f t := by
    dsimp only [G]
    congr 1
    exact Set.projIcc_of_mem (by norm_num) t.property
  have hu : (∫ t:Interval,f t)=∫ t in (0:ℝ)..1,G t := by
    calc
      _ = ∫ t:Interval,G (t:ℝ) := integral_congr_ae (Eventually.of_forall (fun t => (he t).symm))
      _ = _ := by rw [integral_subtype measurableSet_Icc,integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  have hp : (∫ t:Interval in prefixSet (1/2),f t)=∫ t in (0:ℝ)..(1/2),G t := by
    rw [← prefix_integral G (by norm_num : (1/2:ℝ)∈Icc (0:ℝ) 1)]
    exact setIntegral_congr_fun (prefixSet_measurable _) (fun t _ => (he t).symm)
  have hr : (∫ t in (1/2:ℝ)..1,G t)=∫ t in (0:ℝ)..(1/2),G t := by
    have hh := intervalIntegral.integral_comp_sub_left G (a := (0:ℝ)) (b := (1/2:ℝ)) 1
    norm_num only [sub_zero,show (1:ℝ)-1/2=1/2 by norm_num] at hh
    rw [← hh]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc (0:ℝ) (1/2) := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1/2)] using ht
    let s : Interval := ⟨t,⟨ht'.1,by linarith [ht'.2]⟩⟩
    calc
      G (1-t) = f (physicalReflection s) := he (physicalReflection s)
      _ = f s := hf s
      _ = G t := (he s).symm
  rw [hu,hp,← intervalIntegral.integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ := volume) 0 (1/2)) (hG.intervalIntegrable (μ := volume) (1/2) 1),hr]
  ring

/-- At every actual complex disk order, the continued energy is exactly the printed twice-half-interval squared-profile integral.
Use: confirms that the holomorphic energy in holo(d) is the original complex article expression, including its factor two.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: evaluate the genuine integration map and apply the proved reflection integral identity to the actual continuous profile square. -/
theorem OrderDisk.persymmetricEnergy_half {a0 r B : ℝ} (D : OrderDisk a0) (hrD : r≤D.radius)
    (hB : 0<B) (hbound : ∀ a:ℂ,‖a-(a0:ℂ)‖≤r → ‖D.GLsolution a‖≤B)
    {a : ℂ} (ha : ‖a-(a0:ℂ)‖≤r) :
    D.persymmetricEnergy a=2*(∫ t:Interval in prefixSet (1/2),(D.profileMap a t)^2) := by
  rw [OrderDisk.persymmetricEnergy,complexProfileIntegral_apply]
  exact reflected_integral_half ((D.profileMap a)^2) (fun t => by
    change (D.profileMap a (physicalReflection t))^2=(D.profileMap a t)^2
    rw [D.profileMap_reflection hrD hB hbound ha])

end
end jacobi.Analytic
