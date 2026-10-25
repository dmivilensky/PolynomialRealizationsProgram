import polyak.FareyPlateau.Plateau.LocationRoot
import Mathlib.Analysis.Real.Sqrt

/-! The large-curvature secular-root limit, along arbitrary filters. -/
noncomputable section
namespace polyak.FareyPlateau
open Levels Filter Set Topology

theorem shiftedEdgeRoot_numerator_bound (C : Chart.CoefficientPoint) {c h a D : ℝ}
    (he : C.val=edgeCoefficients c h a D) (hc : c∈Ioo (-1:ℝ) 1) (hh : 0<h) :
    shiftedEdgeRoot C a*(1+D-c*shiftedEdgeRoot C a)^2 ≤
      (1/(2*h))*(|1+D|+|c|/(2*h))^2 := by
  have hr := (shiftedEdgeRoot_pos C he).le
  have hb := shiftedEdgeRoot_bound C he hc hh
  have hab : |1+D-c*shiftedEdgeRoot C a|≤|1+D|+|c|/(2*h) := by
    calc
      _≤|1+D|+|c*shiftedEdgeRoot C a| := abs_sub _ _
      _=|1+D|+|c| * shiftedEdgeRoot C a := by rw [abs_mul,abs_of_nonneg hr]
      _≤_ := by simpa only [div_eq_mul_inv,mul_assoc,one_mul,add_comm] using
        add_le_add_left (mul_le_mul_of_nonneg_left hb (abs_nonneg c)) |1+D|
  have hs : (1+D-c*shiftedEdgeRoot C a)^2≤(|1+D|+|c|/(2*h))^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hab
  exact mul_le_mul hb hs (sq_nonneg _) (by positivity)

theorem shiftedEdgeRoot_tendsto {ι : Type*} {l : Filter ι}
    (C : ι→Chart.CoefficientPoint) (a : ι→ℝ) {c h D : ℝ}
    (he : ∀i,(C i).val=edgeCoefficients c h (a i) D)
    (hc : c∈Ioo (-1:ℝ) 1) (hh : 0<h) (ha : Tendsto a l atTop) :
    Tendsto (fun i=>shiftedEdgeRoot (C i) (a i)) l (𝓝 (edgeRootLimit c h)) := by
  let r := fun i=>shiftedEdgeRoot (C i) (a i)
  let err := fun i=>r i*(1+D-c*r i)^2/(2*a i+r i)
  have hr (i) : 0<r i := shiftedEdgeRoot_pos (C i) (he i)
  have hs : 0<1-c^2 := by
    nlinarith [mul_pos (sub_pos.mpr hc.2) (show 0<1+c by linarith [hc.1])]
  have hden : Tendsto (fun i=>2*a i+r i) l atTop := by
    apply tendsto_atTop_mono (fun i=>show 2*a i≤2*a i+r i by linarith [hr i])
    exact ha.const_mul_atTop (by norm_num)
  have herr : Tendsto err l (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero
      (Eventually.of_forall (fun i=>show 0≤r i*(1+D-c*r i)^2 by exact mul_nonneg (hr i).le (sq_nonneg _)))
      (Eventually.of_forall (fun i=>shiftedEdgeRoot_numerator_bound (C i) (he i) hc hh)) hden
  have hrep (i) : r i=(Real.sqrt (h^2+(1-c^2)*(1-err i))-h)/(1-c^2) := by
    have hid := shiftedEdgeRoot_identity (C i) (he i)
    change (1-c^2)*(r i)^2+2*h*r i+err i=1 at hid
    have heq : h^2+(1-c^2)*(1-err i)=(h+(1-c^2)*r i)^2 := by nlinarith [hid]
    rw [heq,Real.sqrt_sq (by exact add_nonneg hh.le (mul_nonneg hs.le (hr i).le) : 0≤h+(1-c^2)*r i)]
    field_simp [hs.ne']
    ring
  have hlim : Tendsto r l (𝓝 ((Real.sqrt (h^2+(1-c^2))-h)/(1-c^2))) := by
    have hinner : Tendsto (fun i=>h^2+(1-c^2)*(1-err i)) l
        (𝓝 (h^2+(1-c^2)*(1-0))) :=
      tendsto_const_nhds.add ((tendsto_const_nhds.sub herr).const_mul (1-c^2))
    have houter := (Real.continuous_sqrt.tendsto _).comp hinner
    have hfinal := (houter.sub_const h).div_const (1-c^2)
    convert hfinal using 1
    · funext i; exact hrep i
    · simp
  have heqlimit : edgeRootLimit c h=(Real.sqrt (h^2+(1-c^2))-h)/(1-c^2) := by
    unfold edgeRootLimit
    have hsq := Real.sq_sqrt (show 0≤h^2+(1-c^2) by positivity)
    have hd : Real.sqrt (h^2+(1-c^2))+h≠0 := by positivity
    have hi : h^2+1-c^2=h^2+(1-c^2) := by ring
    rw [hi]
    field_simp [hs.ne',hd]
    nlinarith
  rw [heqlimit]
  exact hlim

end polyak.FareyPlateau
