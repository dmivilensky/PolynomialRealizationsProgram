import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
Article: jacobi, Proposition B.1.
An elementary two-sine identity converts genuine angular gaps and
endpoint distances into the precise quadratic node-gap scale. These
bounds are applied to both the actual Jacobi nodes and their explicit
corrected trigonometric model.
Source: Jordan's inequality and the cosine-difference identity.
Use: treats the midpoint of any pair of actual or model angles uniformly near both spectral edges.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set

/-- Sine dominates the smaller endpoint distance on its full nonnegative principal interval.
Use: treats the midpoint of any pair of actual or model angles uniformly near both spectral edges.
Article: jacobi, Proposition B.1.
Source: Jordan's inequality.
Proof: use the community concavity estimate on [0,pi/2]; on the other
half reflect the actual argument through pi/2 and use sin(pi-x)=sin(x). -/
theorem sine_endpoint_lower {x : ℝ} (hx : x∈Icc 0 Real.pi) :
    (2/Real.pi)*min x (Real.pi-x)≤sin x := by
  by_cases hh : x≤Real.pi/2
  · rw [min_eq_left (by linarith)]
    exact Real.mul_le_sin hx.1 hh
  · rw [min_eq_right (by linarith)]
    simpa only [Real.sin_pi_sub] using Real.mul_le_sin
      (x := Real.pi-x) (by linarith [hx.2]) (by linarith)

/-- Two genuine principal angles with both midpoint endpoint distances bounded below have the exact quadratic cosine separation scale.
Use: converts the proved original angular gap and distance bounds into the node-gap assertions of Proposition B.1 (c).
Article: jacobi, Proposition B.1.
Proof: write the cosine difference as twice the product of the midpoint
sine and half-gap sine. Jordan's inequality bounds the first by s/pi
from both endpoints and the second by (v-u)/pi. Both factors are nonnegative. -/
theorem cosine_gap_lower {u v s : ℝ} (hu : u∈Icc 0 Real.pi) (hv : v∈Icc 0 Real.pi)
    (huv : u≤v) (hs : 0≤s) (hleft : s≤u+v) (hright : s≤2*Real.pi-u-v) :
    2*s*(v-u)/Real.pi^2≤|cos u-cos v| := by
  -- The midpoint carries the sum-of-indices edge scale, while the half-gap carries the difference-of-indices scale.
  have hm : (u+v)/2∈Icc 0 Real.pi := ⟨by linarith [hu.1,hv.1],by linarith [hu.2,hv.2]⟩
  have hmid : s/Real.pi≤sin ((u+v)/2) := by
    have he := sine_endpoint_lower hm
    have hmin : s/2≤min ((u+v)/2) (Real.pi-(u+v)/2) := le_min (by linarith) (by linarith)
    have hh := mul_le_mul_of_nonneg_left hmin (show 0≤2/Real.pi by positivity)
    calc
      _ = (2/Real.pi)*(s/2) := by ring
      _ ≤ _ := hh
      _ ≤ _ := he
  have hdiff : (v-u)/Real.pi≤sin ((v-u)/2) := by
    have he := Real.mul_le_sin (x := (v-u)/2) (by linarith) (by linarith [hv.2,hu.1])
    convert he using 1
    ring
  have hsinmid : 0≤sin ((u+v)/2) := Real.sin_nonneg_of_nonneg_of_le_pi hm.1 hm.2
  have hsindiff : 0≤sin ((v-u)/2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hv.2,hu.1,Real.pi_pos])
  have hid : cos u-cos v=2*sin ((u+v)/2)*sin ((v-u)/2) := by
    rw [Real.cos_sub_cos,show (u-v)/2= -((v-u)/2) by ring,Real.sin_neg]
    ring
  rw [hid,abs_of_nonneg (by positivity)]
  have hh := mul_le_mul hmid hdiff (by positivity : 0≤(v-u)/Real.pi) hsinmid
  calc
    _ = 2*((s/Real.pi)*((v-u)/Real.pi)) := by field_simp
    _ ≤ _ := by nlinarith

end
end jacobi.Oscillation
