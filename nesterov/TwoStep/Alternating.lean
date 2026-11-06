import nesterov.TwoStep.AsymptoticsModel
import nesterov.Momentum.RestQuadratic
import nesterov.Quadratic.Rate
import Mathlib.Analysis.Asymptotics.Lemmas

/-! Lemma altmode: the actual sign-alternating largest-curvature root. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set Asymptotics
open scoped Topology

def alternatingDelta (e σ : ℝ) : ℝ := 2*e/(σ+Real.sqrt (σ^2-4*e))

theorem alternatingDelta_eq {e σ : ℝ} (hσ : 0<σ) (_he : 0<e) (hd : 4*e<σ^2) :
    alternatingDelta e σ=(σ-Real.sqrt (σ^2-4*e))/2 := by
  have hs := Real.sq_sqrt (by linarith : 0≤σ^2-4*e)
  have hn : σ+Real.sqrt (σ^2-4*e)≠0 := ne_of_gt (by positivity)
  unfold alternatingDelta
  apply (div_eq_iff hn).mpr
  nlinarith

theorem alternatingDelta_properties {e σ : ℝ} (hσ : 0<σ) (he : 0<e) (hd : 4*e<σ^2) :
    0<alternatingDelta e σ ∧ alternatingDelta e σ<σ/2 ∧
      (alternatingDelta e σ)^2-σ*alternatingDelta e σ+e=0 := by
  have hp : 0<alternatingDelta e σ := div_pos (by positivity) (by positivity)
  rw [alternatingDelta_eq hσ he hd] at hp ⊢
  have hs := Real.sq_sqrt (by linarith : 0≤σ^2-4*e)
  have hspos := Real.sqrt_pos.mpr (by linarith : 0<σ^2-4*e)
  exact ⟨hp,by linarith,by nlinarith⟩

theorem alternatingDelta_tendsto {A : Type*} {l : Filter A} {e σ : A→ℝ} {σ₀ : ℝ}
    (he : Tendsto e l (𝓝 0)) (hσ : Tendsto σ l (𝓝 σ₀)) (hσ₀ : 0<σ₀) :
    Tendsto (fun a=>alternatingDelta (e a) (σ a)) l (𝓝 0) := by
  have hd := ((hσ.pow 2).sub (he.const_mul 4)).sqrt
  have hh := (he.const_mul 2).div (hσ.add hd)
    (show σ₀+Real.sqrt (σ₀^2-4*0)≠0 by positivity)
  simp only [mul_zero,zero_div] at hh
  convert hh using 1
  funext a
  rfl

theorem alternatingDelta_ratio_tendsto {A : Type*} {l : Filter A} {e σ : A→ℝ} {σ₀ : ℝ}
    (he : Tendsto e l (𝓝 0)) (hσ : Tendsto σ l (𝓝 σ₀)) (hσ₀ : 0<σ₀)
    (hene : ∀ᶠ a in l,e a≠0) :
    Tendsto (fun a=>alternatingDelta (e a) (σ a)/e a) l (𝓝 (1/σ₀)) := by
  have hd := ((hσ.pow 2).sub (he.const_mul 4)).sqrt
  have hden : σ₀+Real.sqrt (σ₀^2-4*0)≠0 := by positivity
  have hh := (tendsto_const_nhds (x:=(2:ℝ))).div (hσ.add hd) hden
  have hv : 2/(σ₀+Real.sqrt (σ₀^2-4*0))=1/σ₀ := by
    rw [mul_zero,sub_zero,Real.sqrt_sq hσ₀.le]
    field_simp
    ring
  rw [hv] at hh
  apply hh.congr'
  filter_upwards [hene] with a ha
  change 2/(σ a+Real.sqrt (σ a^2-4*e a))=alternatingDelta (e a) (σ a)/e a
  unfold alternatingDelta
  field_simp

/-- The remainder in the rationalized small-root formula is quadratic in the gap. -/
theorem alternatingDelta_approx {A : Type*} {l : Filter A} {e σ : A→ℝ} {σ₀ : ℝ}
    (he : Tendsto e l (𝓝 0)) (hσ : Tendsto σ l (𝓝 σ₀)) (hσ₀ : 0<σ₀)
    (hep : ∀ᶠ a in l,0<e a) :
    (fun a=>alternatingDelta (e a) (σ a)-e a/σ a) =O[l] (fun a=>(e a)^2) := by
  let d : A→ℝ := fun a=>alternatingDelta (e a) (σ a)
  have ht : Tendsto (d/e) l (𝓝 (1/σ₀)) := by
    convert alternatingDelta_ratio_tendsto he hσ hσ₀ (hep.mono fun _ h=>h.ne') using 1
  have hd : d =O[l] e := isBigO_of_div_tendsto_nhds
    (hep.mono fun _ ha hz=>False.elim (ha.ne' hz)) _ ht
  have hi : (fun a=>(σ a)⁻¹) =O[l] (fun _ : A=>(1:ℝ)) :=
    (hσ.inv₀ hσ₀.ne').isBigO_one ℝ
  have hb := (hd.pow 2).mul hi
  have hdisc : Tendsto (fun a=>(σ a)^2-4*e a) l (𝓝 (σ₀^2)) := by
    simpa only [mul_zero,sub_zero] using (hσ.pow 2).sub (he.const_mul 4)
  have heq : (fun a=>alternatingDelta (e a) (σ a)-e a/σ a)=ᶠ[l]
      (fun a=>(d a)^2*(σ a)⁻¹) := by
    filter_upwards [hep,hσ.eventually (eventually_gt_nhds hσ₀),
      hdisc.eventually (eventually_gt_nhds (sq_pos_of_pos hσ₀))] with a hea hsa hda
    have hroot := (alternatingDelta_properties hsa hea (by linarith : 4*e a<(σ a)^2)).2.2
    dsimp [d]
    field_simp
    linear_combination -hroot
  have hb' : (fun a=>(d a)^2*(σ a)⁻¹) =O[l] (fun a=>(e a)^2) := by
    simpa only [mul_one] using hb
  exact hb'.congr' heq.symm (Filter.EventuallyEq.refl _ _)

/-- Exact root locations and the dominant scalar radius for the alternating mode. -/
theorem alternating_roots {S Q δ : ℝ} (hδ : δ^2-(2+S)*δ+(1+S+Q)=0)
    (hsmall : 0<δ ∧ δ<1) (hother : |1+S-δ|<1-δ) :
    ((-1+δ:ℝ):ℂ)^2-(S:ℂ)*((-1+δ:ℝ):ℂ)+(Q:ℂ)=0 ∧
    ((1+S-δ:ℝ):ℂ)^2-(S:ℂ)*((1+S-δ:ℝ):ℂ)+(Q:ℂ)=0 ∧
    polyak.General.rootRadius S Q=1-δ := by
  have h₁ : (-1+δ)^2-S*(-1+δ)+Q=0 := by nlinarith
  have h₂ : (1+S-δ)^2-S*(1+S-δ)+Q=0 := by nlinarith
  have hc₁ : ((-1+δ:ℝ):ℂ)^2-(S:ℂ)*((-1+δ:ℝ):ℂ)+(Q:ℂ)=0 := by exact_mod_cast h₁
  have hc₂ : ((1+S-δ:ℝ):ℂ)^2-(S:ℂ)*((1+S-δ:ℝ):ℂ)+(Q:ℂ)=0 := by exact_mod_cast h₂
  refine ⟨hc₁,hc₂,?_⟩
  apply le_antisymm
  · obtain ⟨z,hz,he⟩ := (Quadratic.scalarRootRadius_isGreatest S Q).1
    have hsum : ((-1+δ:ℝ):ℂ)+((1+S-δ:ℝ):ℂ)=(S:ℂ) := by push_cast;ring
    have hprod : ((-1+δ:ℝ):ℂ)*((1+S-δ:ℝ):ℂ)=(Q:ℂ) := by
      have hh : (-1+δ)*(1+S-δ)=Q := by nlinarith
      exact_mod_cast hh
    rcases Quadratic.root_eq_or_eq hsum hprod hz with rfl|rfl
    · rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : -1+δ<0)]
      ring_nf
      exact le_rfl
    · rw [he,Complex.norm_real,Real.norm_eq_abs]
      exact hother.le
  · have hh := (Quadratic.scalarRootRadius_isGreatest S Q).2 ⟨((-1+δ:ℝ):ℂ),hc₁,rfl⟩
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : -1+δ<0)] at hh
    linarith

def largestCurvatureGap (q : Momentum.Tuning) : ℝ :=
  1+Quadratic.S q.beta q.tau q.stepSize 1+Quadratic.Q q.beta q.tau q.stepSize 1

def alternatingShift (q : Momentum.Tuning) : ℝ :=
  alternatingDelta (largestCurvatureGap q) (2+Quadratic.S q.beta q.tau q.stepSize 1)

theorem largestCurvatureGap_eq (q : Momentum.Tuning) :
    largestCurvatureGap q=2*(1+q.beta)-q.stepSize*(1+2*q.tau) := by
  unfold largestCurvatureGap Quadratic.S Quadratic.Q
  ring

/-- Lemma altmode(a), including the literal from-rest scalar nth-root limsup. -/
theorem alternating_mode_eventually {A : Type*} {l : Filter A}
    {q : A→Momentum.Tuning} {S₀ : ℝ}
    (hS : Tendsto (fun a=>Quadratic.S (q a).beta (q a).tau (q a).stepSize 1) l (𝓝 S₀))
    (he : Tendsto (fun a=>largestCurvatureGap (q a)) l (𝓝 0))
    (hep : ∀ᶠ a in l,0<largestCurvatureGap (q a)) (hS₀ : S₀∈Ioo (-2:ℝ) 0) :
    Tendsto (fun a=>alternatingShift (q a)) l (𝓝 0) ∧
    Tendsto (fun a=>alternatingShift (q a)/largestCurvatureGap (q a)) l (𝓝 (1/(2+S₀))) ∧
    ∀ᶠ a in l,
      0<alternatingShift (q a) ∧ alternatingShift (q a)<1 ∧
      Quadratic.characteristic (q a).beta (q a).tau (q a).stepSize 1
        ((-1+alternatingShift (q a):ℝ):ℂ)=0 ∧
      Quadratic.characteristic (q a).beta (q a).tau (q a).stepSize 1
        ((1+Quadratic.S (q a).beta (q a).tau (q a).stepSize 1-alternatingShift (q a):ℝ):ℂ)=0 ∧
      |1+Quadratic.S (q a).beta (q a).tau (q a).stepSize 1-alternatingShift (q a)|<
        1-alternatingShift (q a) ∧
      Quadratic.scalarRadius (q a).beta (q a).tau (q a).stepSize 1=1-alternatingShift (q a) ∧
      limsup (fun n : ℕ=>|Momentum.iterate (fun x : ℝ=>x) (q a).beta (q a).tau
        (q a).stepSize 1 n|^((n:ℝ)⁻¹)) atTop=1-alternatingShift (q a) := by
  have hσ := (tendsto_const_nhds (x:=(2:ℝ))).add hS
  have hσ₀ : 0<2+S₀ := by linarith [hS₀.1]
  have hd : Tendsto (fun a=>alternatingShift (q a)) l (𝓝 0) :=
    alternatingDelta_tendsto he hσ hσ₀
  refine ⟨hd,alternatingDelta_ratio_tendsto he hσ hσ₀ (hep.mono fun _ h=>h.ne'),?_⟩
  have hdisc : Tendsto (fun a=>(2+Quadratic.S (q a).beta (q a).tau (q a).stepSize 1)^2-
      4*largestCurvatureGap (q a)) l (𝓝 ((2+S₀)^2)) := by
    simpa only [mul_zero,sub_zero] using (hσ.pow 2).sub (he.const_mul 4)
  have hother := ((((tendsto_const_nhds (x:=(1:ℝ))).add hS).sub hd).abs).add hd
  have hlim : |1+S₀-0|+0<1 := by rw [sub_zero,add_zero,abs_lt];constructor <;> linarith [hS₀.1,hS₀.2]
  filter_upwards [hep,hσ.eventually (eventually_gt_nhds hσ₀),
    hdisc.eventually (eventually_gt_nhds (sq_pos_of_pos hσ₀)),
    hd.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hother.eventually (eventually_lt_nhds hlim)] with a hea hσa hdisca hda hoa
  obtain ⟨hdpos,_,hroot⟩ := alternatingDelta_properties hσa hea (by linarith :
    4*largestCurvatureGap (q a)<(2+Quadratic.S (q a).beta (q a).tau (q a).stepSize 1)^2)
  change 0<alternatingShift (q a) at hdpos
  change (alternatingShift (q a))^2-
    (2+Quadratic.S (q a).beta (q a).tau (q a).stepSize 1)*alternatingShift (q a)+
    largestCurvatureGap (q a)=0 at hroot
  have ho : |1+Quadratic.S (q a).beta (q a).tau (q a).stepSize 1-alternatingShift (q a)|<
      1-alternatingShift (q a) := by linarith
  obtain ⟨hz₁,hz₂,hrad⟩ := alternating_roots hroot ⟨hdpos,hda⟩ ho
  refine ⟨hdpos,hda,by rwa [Quadratic.characteristic_eq],
    by rwa [Quadratic.characteristic_eq],ho,hrad,?_⟩
  have hh := Momentum.quadratic_iterate_root_limsup (β:=(q a).beta) (τ:=(q a).tau)
    (h:=(q a).stepSize) (lam:=1) (x₀:=1) (q a).step_pos (by norm_num) (by norm_num)
  simpa only [one_mul,Quadratic.scalarRadius,hrad] using hh

end
end nesterov.TwoStep
