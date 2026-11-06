import nesterov.TwoStep.Alternating

/-! The relative-error form of the small alternating-root expansion. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set Asymptotics
open scoped Topology

theorem alternatingDelta_relative_isBigO {A : Type*} {l : Filter A} {e σ : A→ℝ} {σ₀ : ℝ}
    (he : Tendsto e l (𝓝 0)) (hσ : Tendsto σ l (𝓝 σ₀)) (hσ₀ : 0<σ₀)
    (hep : ∀ᶠ a in l,0<e a) :
    (fun a=>σ a*alternatingDelta (e a) (σ a)/e a-1) =O[l] e := by
  let d : A→ℝ := fun a=>alternatingDelta (e a) (σ a)
  have hratio : Tendsto (d/e) l (𝓝 (1/σ₀)) := by
    convert alternatingDelta_ratio_tendsto he hσ hσ₀ (hep.mono fun _ ha=>ha.ne') using 1
  have hd : d =O[l] e := isBigO_of_div_tendsto_nhds
    (hep.mono fun _ ha hz=>False.elim (ha.ne' hz)) _ hratio
  have hb : (fun a=>d a*(d a/e a)) =O[l] e := by
    have hh := hd.mul (hratio.isBigO_one ℝ)
    simp only [mul_one] at hh
    convert hh using 1
  have hdisc : Tendsto (fun a=>(σ a)^2-4*e a) l (𝓝 (σ₀^2)) := by
    simpa only [mul_zero,sub_zero] using (hσ.pow 2).sub (he.const_mul 4)
  have heq : (fun a=>d a*(d a/e a))=ᶠ[l]
      (fun a=>σ a*alternatingDelta (e a) (σ a)/e a-1) := by
    filter_upwards [hep,hσ.eventually (eventually_gt_nhds hσ₀),
      hdisc.eventually (eventually_gt_nhds (sq_pos_of_pos hσ₀))] with a hea hsa hda
    have hroot := (alternatingDelta_properties hsa hea (by linarith : 4*e a<(σ a)^2)).2.2
    dsimp [d]
    field_simp [hea.ne']
    linear_combination hroot
  exact hb.congr' heq (EventuallyEq.refl _ _)

theorem alternatingDelta_relative_identity {e σ : ℝ} (he : e≠0) (hσ : σ≠0) :
    alternatingDelta e σ=(e/σ)*(1+(σ*alternatingDelta e σ/e-1)) := by
  field_simp [he,hσ]
  ring

end
end nesterov.TwoStep
