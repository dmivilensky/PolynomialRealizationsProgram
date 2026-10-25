import polyak.FareyPlateau.Domain.Phase
import polyak.Levels.Geometry.Arccotangent

/-! The actual slope index on the edge depends only on D. -/
noncomputable section
namespace polyak.FareyPlateau.Ray
open General Levels Set Filter
open scoped Topology

def edgeSlope (ω γ D : ℝ) : ℝ :=
  2*(Real.sin γ)^2*(1+D+(Real.cos γ/Real.sin γ)*(Real.cos ω/Real.sin ω))

theorem cotangentFirst_edge (q : Tuning) {ω γ a D : ℝ}
    (hω : ω∈Ioo (0:ℝ) Real.pi) (hγ : γ∈Ioo (0:ℝ) Real.pi)
    (he : Chart.coefficients q=edgeCoefficients (Real.cos ω)
      ((Real.cos γ/Real.sin γ)*Real.sin ω) a D) :
    Geometry.cotangentFirst q ω= -(1+D+(Real.cos γ/Real.sin γ)*(Real.cos ω/Real.sin ω)) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have ht := Real.sin_pos_of_pos_of_lt_pi hγ.1 hγ.2
  have hfun : Geometry.cotangent q=(fun x=>
      ((Real.cos γ/Real.sin γ)*Real.sin ω+(1+D)*(Real.cos x-Real.cos ω)-
        a*(Real.cos x-Real.cos ω)^2)/Real.sin x) := by
    funext x
    rw [Geometry.cotangent,←Chart.eval_coefficients,he,edgeCoefficients_eval]
  have hnum := ((hasDerivAt_const ω ((Real.cos γ/Real.sin γ)*Real.sin ω)).add
    (((Real.hasDerivAt_cos ω).sub_const (Real.cos ω)).const_mul (1+D))).sub
      ((((Real.hasDerivAt_cos ω).sub_const (Real.cos ω)).pow 2).const_mul a)
  have hd := (hnum.div (Real.hasDerivAt_sin ω) hs.ne').deriv
  change deriv (fun x=>
      ((Real.cos γ/Real.sin γ)*Real.sin ω+(1+D)*(Real.cos x-Real.cos ω)-
        a*(Real.cos x-Real.cos ω)^2)/Real.sin x) ω=_ at hd
  rw [←hfun,Geometry.deriv_cotangent q hω] at hd
  rw [hd]
  dsimp only [Pi.add_apply,Pi.sub_apply,Pi.pow_apply]
  norm_num only [sub_self,pow_zero,pow_one,zero_pow (by norm_num : (2:ℕ)≠0),
    mul_zero,zero_mul,sub_zero,add_zero,zero_add,Nat.cast_ofNat]
  field_simp [hs.ne',ht.ne']
  ring

theorem slope_index_edge (q : Tuning) {ω γ a D : ℝ}
    (hω : ω∈Ioo (0:ℝ) Real.pi) (hγ : γ∈Ioo (0:ℝ) Real.pi)
    (he : Chart.coefficients q=edgeCoefficients (Real.cos ω)
      ((Real.cos γ/Real.sin γ)*Real.sin ω) a D)
    (hphase : q.angle ω=γ) :
    2*deriv (Geometry.shiftedAngle q 0) ω=edgeSlope ω γ D := by
  rw [(Geometry.hasDerivAt_shiftedAngle q 0 hω).deriv]
  unfold Geometry.shiftedFirst
  rw [cotangentFirst_edge q hω hγ he]
  have hc : Geometry.cotangent q ω=Real.cos γ/Real.sin γ := by
    rw [Geometry.cotangent,←q.cot_angle hω,hphase]
  rw [hc,add_zero]
  have hs := Real.sin_pos_of_pos_of_lt_pi hγ.1 hγ.2
  have hid : 1+(Real.cos γ/Real.sin γ)^2=1/(Real.sin γ)^2 := by
    field_simp [hs.ne']
    nlinarith [Real.sin_sq_add_cos_sq γ]
  rw [hid]
  unfold edgeSlope
  field_simp [hs.ne']

theorem source_slope_index (q : Tuning) {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k)
    {a D : ℝ} (he : Chart.coefficients q=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) a D) :
    2*deriv (Geometry.shiftedAngle q 0) (Regions.rationalAngle j k)=
      edgeSlope (Regions.rationalAngle j k) (Real.pi/k) D := by
  have hω := Regions.rationalAngle_mem hj hjk
  have hk : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  have hγ : Real.pi/k∈Ioo (0:ℝ) Real.pi :=
    ⟨div_pos Real.pi_pos (by linarith),div_lt_self Real.pi_pos hk⟩
  exact slope_index_edge q hω hγ he (source_edge_phase q hj hjk he)

end polyak.FareyPlateau.Ray
