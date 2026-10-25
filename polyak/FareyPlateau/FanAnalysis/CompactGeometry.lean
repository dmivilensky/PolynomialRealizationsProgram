import polyak.FareyPlateau.FanAnalysis.CompactFamily

/-! Uniform positivity away from the two roots and uniform local convexity.
Both follow from actual joint continuity and compactness of the tuning family. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.CompactFamily.Data
open General Levels Set Filter
open scoped Topology
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
variable {j k : ℕ} (B : CompactFamily.Data X j k)

omit [CompactSpace X] in
include B in
theorem center_interior : Parameters.omega j k∈Ioo (0:ℝ) Real.pi :=
  Actual.frequency_interior (B.adjacent (Classical.choice (inferInstance : Nonempty X)))

omit [CompactSpace X] in
include B in
theorem center_sin_ne_zero : Real.sin (Parameters.omega j k)≠0 := by
  have hi := B.center_interior
  exact (Real.sin_pos_of_pos_of_lt_pi hi.1 hi.2).ne'

omit [CompactSpace X] in
include B in
theorem phase_strip : ∃r : ℝ, 0<r ∧ ∀δ : ℝ, |δ|<r →
    Real.sin (Parameters.omega j k+δ)≠0 ∧
      Real.sin (Parameters.omega j k-((k : ℝ)-1)*δ)≠0 := by
  have hn : ContinuousAt (fun δ : ℝ => Real.sin (Parameters.omega j k+δ)) 0 := by fun_prop
  have hf : ContinuousAt (fun δ : ℝ => Real.sin (Parameters.omega j k-((k : ℝ)-1)*δ)) 0 := by fun_prop
  have hns : Real.sin (Parameters.omega j k+0)≠0 := by simpa only [add_zero] using B.center_sin_ne_zero
  have hfs : Real.sin (Parameters.omega j k-((k : ℝ)-1)*0)≠0 := by simpa only [mul_zero,sub_zero] using B.center_sin_ne_zero
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ((hn.eventually_ne hns).and (hf.eventually_ne hfs))
  exact ⟨r,hr,fun δ hδ => hball (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hδ)⟩

def second (ε : ℝ) (x : X) (δ θ : ℝ) : ℝ :=
  constraintSecond ((k : ℝ)-1) (B.correction x) (B.angle ε 1 x) (B.angle ε (-((k : ℝ)-1)) x) δ θ

omit [CompactSpace X] [Nonempty X] in
theorem zero_second (ε : ℝ) (x : X) (θ : ℝ) : B.second ε x 0 θ=deriv^[2] (Fan.polynomial k) θ := by
  rw [Fan.polynomial_second]
  simp only [second,constraintSecond,B.zero_angle,mul_zero,add_zero]

omit [CompactSpace X] [Nonempty X] in
theorem second_continuousAt (ε : ℝ) (x : X) (δ θ : ℝ)
    (ha : Real.sin (Parameters.omega j k+δ)≠0)
    (hc : Real.sin (Parameters.omega j k-((k : ℝ)-1)*δ)≠0) :
    ContinuousAt (fun p : (ℝ×ℝ)×X => B.second ε p.2 p.1.1 p.1.2) ((δ,θ),x) := by
  have hnear := (B.angle_continuousAt ε 1 x δ (by simpa only [one_mul] using ha)).comp
    (f:=fun p : (ℝ×ℝ)×X => (p.2,p.1.1))
    (show ContinuousAt (fun p : (ℝ×ℝ)×X => (p.2,p.1.1)) ((δ,θ),x) by fun_prop)
  have hfar := (B.angle_continuousAt ε (-((k : ℝ)-1)) x δ (by convert hc using 1; congr 1; ring)).comp
    (f:=fun p : (ℝ×ℝ)×X => (p.2,p.1.1))
    (show ContinuousAt (fun p : (ℝ×ℝ)×X => (p.2,p.1.1)) ((δ,θ),x) by fun_prop)
  have hz : ContinuousAt (fun p : (ℝ×ℝ)×X => B.correction p.2) ((δ,θ),x) :=
    (B.continuous_correction.comp continuous_snd).continuousAt
  have ht : ContinuousAt (fun p : (ℝ×ℝ)×X=>p.1.2) ((δ,θ),x) := by fun_prop
  have hd : ContinuousAt (fun p : (ℝ×ℝ)×X=>p.1.1) ((δ,θ),x) := by fun_prop
  have hcnear := Real.continuous_cos.continuousAt.comp
    (f:=fun p : (ℝ×ℝ)×X=>p.1.2-B.angle ε 1 p.2 p.1.1) (ht.sub hnear)
  have hcfar := Real.continuous_cos.continuousAt.comp
    (f:=fun p : (ℝ×ℝ)×X=>((k:ℝ)-1)*p.1.2+B.angle ε (-((k:ℝ)-1)) p.2 p.1.1)
    ((continuousAt_const.mul ht).add hfar)
  exact ((continuousAt_const.add (hz.mul hd)).mul hcnear).add
    (continuousAt_const.mul hcfar)

theorem uniform_local_convex (ε θ₀ : ℝ) (hpos : 0<deriv^[2] (Fan.polynomial k) θ₀) :
    ∃r : ℝ, 0<r ∧ ∀δ : ℝ, |δ|<r → ∀x : X,
      StrictConvexOn ℝ (Icc (θ₀-r) (θ₀+r)) (B.phi ε x δ) := by
  have he : ∀ᶠ p : ℝ×ℝ in 𝓝 (0,θ₀), ∀x : X, 0<B.second ε x p.1 p.2 := by
    have hh := (isCompact_univ : IsCompact (univ : Set X)).eventually_forall_of_forall_eventually
      (x₀:=(0,θ₀)) (P:=fun p : ℝ×ℝ=>fun x : X=>0<B.second ε x p.1 p.2)
      (fun x (_ : x∈(univ : Set X)) =>
      (B.second_continuousAt ε x 0 θ₀ (by simpa only [add_zero] using B.center_sin_ne_zero)
        (by simpa only [mul_zero,sub_zero] using B.center_sin_ne_zero)).eventually
          (eventually_gt_nhds (show 0<B.second ε x 0 θ₀ by rw [B.zero_second]; exact hpos)))
    simpa only [mem_univ,forall_const] using hh
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨R/2,by positivity,fun δ hδ x => ?_⟩
  apply strictConvexOn_of_deriv2_pos (convex_Icc _ _)
    (fun t _ => (hasDerivAt_constraint _ _ _ _ δ t).continuousAt.continuousWithinAt)
  intro t ht
  rw [constraint_second]
  apply hball (show (δ,t)∈Metric.ball (0,θ₀) R from ?_) x
  rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,max_lt_iff]
  refine ⟨by linarith,?_⟩
  have hi : t∈Icc (θ₀-R/2) (θ₀+R/2) := interior_subset ht
  rw [abs_lt]
  constructor <;> linarith [hi.1,hi.2]

omit [CompactSpace X] [Nonempty X] in
theorem zero_phi (ε : ℝ) (x : X) (θ : ℝ) : B.phi ε x 0 θ=Fan.polynomial k θ := by
  unfold phi constraint Fan.polynomial
  rw [B.zero_angle,B.zero_angle]
  simp only [mul_zero,add_zero]
  ring

theorem uniform_positive_away (ε : ℝ) {r : ℝ} (hr : 0<r) :
    ∀ᶠ δ : ℝ in 𝓝 0, ∀x : X, ∀θ∈awaySet k r, 0<B.phi ε x δ θ := by
  let K : Set (X×ℝ) := univ ×ˢ awaySet k r
  have hK : IsCompact K := isCompact_univ.prod (away_compact k r)
  have hk : 3≤k := (B.adjacent (Classical.choice (inferInstance : Nonempty X))).period_ge
  have he := hK.eventually_forall_of_forall_eventually (x₀:=(0:ℝ))
    (P:=fun δ : ℝ=>fun z : X×ℝ=>0<B.phi ε z.1 δ z.2) (fun z hz =>
    (B.phi_continuousAt ε z.1 0 z.2 (by simpa only [add_zero] using B.center_sin_ne_zero)
      (by simpa only [mul_zero,sub_zero] using B.center_sin_ne_zero)).eventually
      (eventually_gt_nhds (show 0<B.phi ε z.1 0 z.2 by
        rw [B.zero_phi]
        exact polynomial_positive_away hk hr hz.2)))
  filter_upwards [he] with δ hδ x θ hθ
  exact hδ (x,θ) ⟨mem_univ x,hθ⟩

omit [CompactSpace X] in
theorem uniform_frequencies (h : ℝ) : ∀ᶠ δ : ℝ in 𝓝 0,∀x : X,
    (B.adjacent x).frequency+h*δ∈Ioo (0:ℝ) Real.pi := by
  have hc : ContinuousAt (fun δ : ℝ=>Parameters.omega j k+h*δ) 0 := by fun_prop
  have hi : Parameters.omega j k+h*0∈Ioo (0:ℝ) Real.pi := by
    simpa only [mul_zero,add_zero] using B.center_interior
  filter_upwards [hc.eventually (isOpen_Ioo.mem_nhds hi)] with δ hδ x
  exact hδ

omit [CompactSpace X] in
theorem uniform_angle_actual (ε h : ℝ) : ∀ᶠ δ : ℝ in 𝓝 0,∀x : X,
    B.angle ε h x δ=Geometry.shiftedAngle (B.tuning x)
      ((B.adjacent x).edgeShift-(Actual.critical (B.adjacent x)+ε)*δ^2)
      ((B.adjacent x).frequency+h*δ) := by
  filter_upwards [B.uniform_frequencies h] with δ hδ x
  rw [B.angle_actual,Geometry.shiftedAngle_eq_arccotangent _ _ (hδ x)]
  unfold anglePath cotPath
  congr 1
  ring

theorem uniform_mass_and_minimizer (ε : ℝ) : ∀ᶠ δ : ℝ in 𝓝 0,∀x : X,
    0<(k:ℝ)-1+B.correction x*δ ∧
    0<((k:ℝ)-1+B.correction x*δ)*Real.cos (B.angle ε 1 x δ)+
      Real.cos (B.angle ε (-((k:ℝ)-1)) x δ) := by
  let A := B.adjacent (Classical.choice (inferInstance : Nonempty X))
  have hk : (3:ℝ)≤k := by exact_mod_cast A.period_ge
  have hcos := Actual.cos_positive A
  have hx : ∀x∈(univ : Set X),∀ᶠ p : ℝ×X in 𝓝 (0,x),
      0<(k:ℝ)-1+B.correction p.2*p.1 ∧
      0<((k:ℝ)-1+B.correction p.2*p.1)*Real.cos (B.angle ε 1 p.2 p.1)+
        Real.cos (B.angle ε (-((k:ℝ)-1)) p.2 p.1) := by
    intro x _
    have hp : ContinuousAt (fun p : ℝ×X=>(p.2,p.1)) (0,x) := by fun_prop
    have hn := (B.angle_continuousAt ε 1 x 0 (by simpa only [mul_zero,add_zero] using B.center_sin_ne_zero)).comp
      (f:=fun p : ℝ×X=>(p.2,p.1)) hp
    have hf := (B.angle_continuousAt ε (-((k:ℝ)-1)) x 0
      (by simpa only [mul_zero,add_zero] using B.center_sin_ne_zero)).comp
        (f:=fun p : ℝ×X=>(p.2,p.1)) hp
    have hz : ContinuousAt (fun p : ℝ×X=>B.correction p.2) (0,x) :=
      (B.continuous_correction.comp continuous_snd).continuousAt
    have hw : ContinuousAt (fun p : ℝ×X=>(k:ℝ)-1+B.correction p.2*p.1) (0,x) :=
      continuousAt_const.add (hz.mul continuous_fst.continuousAt)
    have hcn := Real.continuous_cos.continuousAt.comp
      (f:=fun p : ℝ×X=>B.angle ε 1 p.2 p.1) hn
    have hcf := Real.continuous_cos.continuousAt.comp
      (f:=fun p : ℝ×X=>B.angle ε (-((k:ℝ)-1)) p.2 p.1) hf
    have hM := (hw.mul hcn).add hcf
    have hmpos : 0<(k:ℝ)-1+B.correction x*0 := by nlinarith
    have hMpos : 0<((k:ℝ)-1+B.correction x*0)*Real.cos (B.angle ε 1 x 0)+
        Real.cos (B.angle ε (-((k:ℝ)-1)) x 0) := by
      rw [B.zero_angle,B.zero_angle]
      have hprod : 0<(k:ℝ)*Real.cos (Real.pi/k) := mul_pos (by linarith) hcos
      nlinarith
    exact (hw.eventually (eventually_gt_nhds hmpos)).and (hM.eventually (eventually_gt_nhds hMpos))
  simpa only [mem_univ,forall_const] using
    (isCompact_univ : IsCompact (univ : Set X)).eventually_forall_of_forall_eventually
      (x₀:=(0:ℝ))
      (P:=fun δ : ℝ=>fun x : X=>0<(k:ℝ)-1+B.correction x*δ ∧
        0<((k:ℝ)-1+B.correction x*δ)*Real.cos (B.angle ε 1 x δ)+
          Real.cos (B.angle ε (-((k:ℝ)-1)) x δ)) hx

end polyak.FareyPlateau.FanAnalysis.CompactFamily.Data
