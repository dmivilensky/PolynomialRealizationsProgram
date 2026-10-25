import polyak.GapEdges.Junction.Curve

/-! The junction lemma for the unrestricted arccotangent polynomial profile.
No tuning or global endpoint signs are assumed. -/
noncomputable section
namespace polyak.GapEdges.Junction
open Levels Set Filter
open scoped Topology

def profileCotangent (a t₁ t₂ : ℝ) : ℝ→ℝ :=
  Geometry.polyCotangent (1-a*t₁*t₂) (1+a*(t₁+t₂)) (-a)
def profileCotangentFirst (a t₁ t₂ : ℝ) : ℝ→ℝ :=
  Geometry.polyCotangentFirst (1-a*t₁*t₂) (1+a*(t₁+t₂)) (-a)
def profileCotangentSecond (a t₁ t₂ : ℝ) : ℝ→ℝ :=
  Geometry.polyCotangentSecond (1-a*t₁*t₂) (1+a*(t₁+t₂)) (-a)
def profileAngle (a t₁ t₂ x : ℝ) : ℝ :=
  Geometry.arccotangent (profileCotangent a t₁ t₂ x)
def profileAngleFirst (a t₁ t₂ x : ℝ) : ℝ :=
  -profileCotangentFirst a t₁ t₂ x/(1+(profileCotangent a t₁ t₂ x)^2)
def profileAngleSecond (a t₁ t₂ x : ℝ) : ℝ :=
  -profileCotangentSecond a t₁ t₂ x/(1+(profileCotangent a t₁ t₂ x)^2)+
    2*profileCotangent a t₁ t₂ x*(profileCotangentFirst a t₁ t₂ x)^2/
      (1+(profileCotangent a t₁ t₂ x)^2)^2

theorem profileCotangent_eq (a t₁ t₂ x : ℝ) :
    profileCotangent a t₁ t₂ x=
      (1+Real.cos x-a*(Real.cos x-t₁)*(Real.cos x-t₂))/Real.sin x := by
  unfold profileCotangent Geometry.polyCotangent
  congr 1
  ring

theorem hasDerivAt_profileAngle (a t₁ t₂ : ℝ) {x : ℝ} (hx : Real.sin x≠0) :
    HasDerivAt (profileAngle a t₁ t₂) (profileAngleFirst a t₁ t₂ x) x := by
  have hc : HasDerivAt (profileCotangent a t₁ t₂) (profileCotangentFirst a t₁ t₂ x) x :=
    Geometry.hasDerivAt_polyCotangent (1-a*t₁*t₂) (1+a*(t₁+t₂)) (-a) hx
  have hh := (Geometry.hasDerivAt_arccotangent (profileCotangent a t₁ t₂ x)).comp x hc
  convert hh using 1
  · rfl
  · dsimp [profileAngleFirst,profileCotangent,profileCotangentFirst]
    ring

theorem hasDerivAt_profileAngleFirst (a t₁ t₂ : ℝ) {x : ℝ} (hx : Real.sin x≠0) :
    HasDerivAt (profileAngleFirst a t₁ t₂) (profileAngleSecond a t₁ t₂ x) x := by
  have hc : HasDerivAt (profileCotangent a t₁ t₂) (profileCotangentFirst a t₁ t₂ x) x :=
    Geometry.hasDerivAt_polyCotangent (1-a*t₁*t₂) (1+a*(t₁+t₂)) (-a) hx
  have h₁ : HasDerivAt (profileCotangentFirst a t₁ t₂) (profileCotangentSecond a t₁ t₂ x) x :=
    Geometry.hasDerivAt_polyCotangentFirst (1-a*t₁*t₂) (1+a*(t₁+t₂)) (-a) hx
  have hd : HasDerivAt (fun y=>1+(profileCotangent a t₁ t₂ y)^2)
      (2*profileCotangent a t₁ t₂ x*profileCotangentFirst a t₁ t₂ x) x := by
    convert (hc.pow 2).const_add 1 using 1; ring
  unfold profileAngleFirst profileAngleSecond
  convert h₁.neg.div hd (by positivity : 1+(profileCotangent a t₁ t₂ x)^2≠0) using 1
  simp only [Pi.neg_apply]
  field_simp
  ring

theorem profile_second (a t₁ t₂ : ℝ) {x : ℝ} (hx : Real.sin x≠0) :
    deriv^[2] (profileAngle a t₁ t₂) x=profileAngleSecond a t₁ t₂ x := by
  have he : deriv (profileAngle a t₁ t₂) =ᶠ[𝓝 x] profileAngleFirst a t₁ t₂ := by
    filter_upwards [Real.continuous_sin.continuousAt.eventually_ne hx] with y hy
    exact (hasDerivAt_profileAngle a t₁ t₂ hy).deriv
  change deriv (deriv (profileAngle a t₁ t₂)) x=_
  rw [he.deriv_eq]
  exact (hasDerivAt_profileAngleFirst a t₁ t₂ hx).deriv

theorem profile_cotangent_jets {a t₂ c : ℝ}
    (hc : c∈Ioo 0 (Real.pi/2)) :
    profileCotangent a (Real.cos (2*c)) t₂ (2*c)=Real.cos c/Real.sin c ∧
    profileCotangentFirst a (Real.cos (2*c)) t₂ (2*c)= -1/(2*Real.sin c^2)+a*(Real.cos (2*c)-t₂) ∧
    profileCotangentSecond a (Real.cos (2*c)) t₂ (2*c)=Real.cos c/(2*Real.sin c^3)+
      a*(Real.cos (2*c)^2+Real.cos (2*c)*t₂-2)/(2*Real.sin c*Real.cos c) := by
  have hs : 0<Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hcos : 0<Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [hc.1,Real.pi_pos],hc.2⟩
  have htr := Real.sin_sq_add_cos_sq c
  have hs2 : Real.sin c^2=1-Real.cos c^2 := by nlinarith
  have hs4 : Real.sin c^4=(1-Real.cos c^2)^2 := by
    rw [show (4:ℕ)=2*2 by decide,pow_mul,hs2]
  dsimp [profileCotangent,profileCotangentFirst,profileCotangentSecond,
    Geometry.polyCotangent,Geometry.polyCotangentFirst,Geometry.polyCotangentSecond]
  rw [Real.sin_two_mul,Real.cos_two_mul]
  constructor
  · field_simp
    nlinarith [htr]
  constructor
  · field_simp
    ring_nf
    simp only [hs2]
    ring
  · field_simp
    ring_nf
    simp only [hs2]
    ring


theorem generic_junction_angle_jets {a t₂ c : ℝ}
    (hc : c∈Ioo 0 (Real.pi/2)) :
    profileAngle a (Real.cos (2*c)) t₂ (2*c)=c ∧
    deriv (profileAngle a (Real.cos (2*c)) t₂) (2*c)-1/2 =
      -a*(Real.cos (2*c)-t₂)*Real.sin c^2 ∧
    deriv^[2] (profileAngle a (Real.cos (2*c)) t₂) (2*c)=
      -(1/2)*(Real.cos c/Real.sin c)+
        (a/2)*(Real.sin c/Real.cos c)*(2-Real.cos (2*c)^2-Real.cos (2*c)*t₂)+
        2*(deriv (profileAngle a (Real.cos (2*c)) t₂) (2*c))^2*(Real.cos c/Real.sin c) := by
  have hω : 2*c∈Ioo 0 Real.pi := ⟨by linarith [hc.1],by linarith [hc.2]⟩
  have hsω : Real.sin (2*c)≠0 := (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2).ne' 
  have hs : 0<Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc.1 (by linarith [hc.2,Real.pi_pos])
  have hcos : 0<Real.cos c := Real.cos_pos_of_mem_Ioo ⟨by linarith [hc.1,Real.pi_pos],hc.2⟩
  have htr := Real.sin_sq_add_cos_sq c
  obtain ⟨h0,h1,h2⟩ := profile_cotangent_jets (a:=a) (t₂:=t₂) hc
  have hf : deriv (profileAngle a (Real.cos (2*c)) t₂) (2*c)=
      1/2-a*(Real.cos (2*c)-t₂)*Real.sin c^2 := by
    rw [(hasDerivAt_profileAngle a (Real.cos (2*c)) t₂ hsω).deriv,profileAngleFirst,h0,h1]
    have he : 1+(Real.cos c/Real.sin c)^2=1/Real.sin c^2 := by
      field_simp
      nlinarith
    rw [he]
    field_simp
    ring
  constructor
  · apply Geometry.angle_eq_of_cot_eq (Geometry.arccotangent_mem _)
      ⟨hc.1,by linarith [hc.2,Real.pi_pos]⟩
    rw [Geometry.cot_arccotangent,h0]
  constructor
  · linarith
  · rw [profile_second a (Real.cos (2*c)) t₂ hsω,profileAngleSecond,h0,h1,h2,hf]
    have he : 1+(Real.cos c/Real.sin c)^2=1/Real.sin c^2 := by
      field_simp
      nlinarith
    rw [he]
    field_simp
    ring

end polyak.GapEdges.Junction
