import nesterov.Corner.Model

/-! The source real-root expansion also covers negative or zero limiting margins. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology
variable {A : Type*} {l : Filter A} {θ : ℝ} (F : Scaling A l θ 2 (1/2))

def cornerRoot (p : A) : ℝ := -1+alternatingShift (F.tuning p)

theorem corner_S_tendsto :
    Tendsto (fun p=>Quadratic.S (F.tuning p).beta (F.tuning p).tau (F.tuning p).stepSize 1)
      l (𝓝 (-1)) := by
  convert F.boundary_S_tendsto (by norm_num : (2:ℝ)*(1+2*(1/2))=4) using 1
  norm_num

theorem corner_gap_scaled_tendsto {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b)) :
    Tendsto (fun p=>largestCurvatureGap (F.tuning p)/F.epsilon p) l
      (𝓝 (Corner.cpi θ a b)) := by
  have h := (F.corner_margin_tendsto ha hb).sub (F.theta_tendsto.const_mul 2)
  have he : 4*a+2*b-2*θ=Corner.cpi θ a b := by unfold Corner.cpi;ring
  rw [he] at h
  exact h.congr' (F.stability_gap_scaled_exact.mono fun _ h=>h.symm)

private theorem small_root_identity {e σ : ℝ} (hσ : 0<σ) (hd : 4*e<σ^2) :
    (alternatingDelta e σ)^2-σ*alternatingDelta e σ+e=0 := by
  have hsq := Real.sq_sqrt (show 0≤σ^2-4*e by linarith)
  have hn : σ+Real.sqrt (σ^2-4*e)≠0 := ne_of_gt (by positivity)
  have heq : alternatingDelta e σ=(σ-Real.sqrt (σ^2-4*e))/2 := by
    unfold alternatingDelta
    apply (div_eq_iff hn).mpr
    nlinarith
  rw [heq]
  nlinarith

theorem corner_root_exact : ∀ᶠ p in l,
    realCharacteristic (F.tuning p).beta (F.tuning p).tau (F.tuning p).stepSize 1 (F.cornerRoot p)=0 := by
  have he := F.boundary_gap_tendsto (by norm_num : (2:ℝ)*(1+2*(1/2))=4)
  have hs := (F.corner_S_tendsto.const_add 2)
  have hd := (hs.pow 2).sub (he.const_mul 4)
  have hs' : Tendsto (fun p=>2+Quadratic.S (F.tuning p).beta (F.tuning p).tau
      (F.tuning p).stepSize 1) l (𝓝 1) := by
    convert hs using 1
    norm_num
  have hd' : Tendsto (fun p=>(2+Quadratic.S (F.tuning p).beta (F.tuning p).tau
      (F.tuning p).stepSize 1)^2-4*largestCurvatureGap (F.tuning p)) l (𝓝 1) := by
    convert hd using 1
    norm_num
  filter_upwards [hs'.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1)),
    hd'.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))] with p hp hd
  have hroot := small_root_identity hp (by linarith : 4*largestCurvatureGap (F.tuning p)<
    (2+Quadratic.S (F.tuning p).beta (F.tuning p).tau (F.tuning p).stepSize 1)^2)
  change (alternatingShift (F.tuning p))^2-
    (2+Quadratic.S (F.tuning p).beta (F.tuning p).tau (F.tuning p).stepSize 1)*
      alternatingShift (F.tuning p)+largestCurvatureGap (F.tuning p)=0 at hroot
  have hgap : largestCurvatureGap (F.tuning p)=1+
      Quadratic.S (F.tuning p).beta (F.tuning p).tau (F.tuning p).stepSize 1+
      Quadratic.Q (F.tuning p).beta (F.tuning p).tau (F.tuning p).stepSize 1 := by
    rw [largestCurvatureGap_eq]
    unfold Quadratic.S Quadratic.Q
    ring
  rw [hgap] at hroot
  unfold cornerRoot realCharacteristic
  nlinarith

theorem corner_root_scaled_tendsto {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b)) :
    Tendsto (fun p=>(F.cornerRoot p+1)/F.epsilon p) l
      (𝓝 (Corner.cpi θ a b)) := by
  have he := F.boundary_gap_tendsto (by norm_num : (2:ℝ)*(1+2*(1/2))=4)
  have hs : Tendsto (fun p=>2+Quadratic.S (F.tuning p).beta (F.tuning p).tau
      (F.tuning p).stepSize 1) l (𝓝 1) := by
    convert F.corner_S_tendsto.const_add 2 using 1
    norm_num
  have hdisc := ((hs.pow 2).sub (he.const_mul 4)).sqrt
  have hden := hs.add hdisc
  have hf := (tendsto_const_nhds (x:=(2:ℝ))).div hden (by norm_num : (1:ℝ)+Real.sqrt (1^2-4*0)≠0)
  have hf' : Tendsto (fun p=>2/(2+Quadratic.S (F.tuning p).beta (F.tuning p).tau
      (F.tuning p).stepSize 1+Real.sqrt ((2+Quadratic.S (F.tuning p).beta (F.tuning p).tau
        (F.tuning p).stepSize 1)^2-4*largestCurvatureGap (F.tuning p)))) l (𝓝 1) := by
    convert hf using 1
    norm_num
  have h := hf'.mul (F.corner_gap_scaled_tendsto ha hb)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [F.epsilon_pos] with p hp
  unfold cornerRoot alternatingShift alternatingDelta
  field_simp
  ring

end
end nesterov.TwoStep.Scaling
