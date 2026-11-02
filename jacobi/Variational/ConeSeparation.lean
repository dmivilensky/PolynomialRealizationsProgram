import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Article: jacobi, Lemma D.3.
Finite-dimensional Hahn--Banach separation gives nonnegative Fritz John
coefficients for objective, mass and spectral observation. In the slack
case the mass coefficient is zero. This lemma separates only real vectors;
the density-domain and differentiability obligations are discharged in its
variational application.
Source: the geometric Hahn--Banach separation theorem, as proved in mathlib.
Use: the active case also requires a strict mass decrease; the slack case leaves mass unrestricted.
-/
namespace jacobi.Variational
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The open cone of strict objective improvement and strict spectral increase.
Use: the active case also requires a strict mass decrease; the slack case leaves mass unrestricted.
Article: jacobi, Lemma D.3.
-/
def improvementCone (active : Prop) : Set (Fin 3 → ℝ) :=
  {v | v 0<0 ∧ (active → v 1<0) ∧ 0<v 2}

/-- The strict-improvement cone is convex.
Use: licenses the finite-dimensional Hahn--Banach separation for the multiplier proof.
Article: jacobi, Lemma D.3.
Proof: its coordinate inequalities are intersections of open linear halfspaces. -/
theorem improvementCone_convex (active : Prop) : Convex ℝ (improvementCone active) := by
  -- At least one convex coefficient is positive, preserving every strict coordinate inequality.
  intro x hx y hy a b ha hb hab
  have hneg {r s : ℝ} (hr : r<0) (hs : s<0) : a*r+b*s<0 := by
    rcases eq_or_lt_of_le ha with hzero | hpos
    · have hb1 : b=1 := by linarith
      rw [← hzero,hb1,zero_mul,zero_add,one_mul]
      exact hs
    · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hpos hr)
        (mul_nonpos_of_nonneg_of_nonpos hb hs.le)
  refine ⟨?_,?_,?_⟩
  · change a*x 0+b*y 0<0
    exact hneg hx.1 hy.1
  · intro hact
    change a*x 1+b*y 1<0
    exact hneg (hx.2.1 hact) (hy.2.1 hact)
  · change 0<a*x 2+b*y 2
    have h := hneg (neg_neg_of_pos hx.2.2) (neg_neg_of_pos hy.2.2)
    linarith

/-- The strict-improvement cone is open, including when its mass coordinate is omitted.
Use: ensures one of the two separated convex sets is open.
Article: jacobi, Lemma D.3.
Proof: coordinate evaluation is continuous; the inactive mass condition is the entire space. -/
theorem improvementCone_open (active : Prop) : IsOpen (improvementCone active) := by
  -- The slack mass case removes its halfspace rather than imposing an artificial strict condition.
  by_cases h : active
  · change IsOpen {v : Fin 3 → ℝ | v 0<0 ∧ (active → v 1<0) ∧ 0<v 2}
    simpa only [h,true_implies,ofPred_and] using
      ((isOpen_lt (continuous_apply 0) continuous_const).inter
        ((isOpen_lt (continuous_apply 1) continuous_const).inter
          (isOpen_lt continuous_const (continuous_apply 2))))
  · simpa only [improvementCone,h,false_implies,and_true,true_and,ofPred_and] using
      (isOpen_lt (continuous_apply 0) continuous_const).inter
        (isOpen_lt continuous_const (continuous_apply 2))

/-- The three actual coordinate coefficients determine any continuous real functional on R^3.
Use: reads the separating functional as objective, mass and spectral multipliers.
Article: jacobi, Lemma D.3.
Proof: expand a vector in the three coordinate vectors and use linearity. -/
theorem functional_three_coordinates (f : StrongDual ℝ (Fin 3 → ℝ)) (v : Fin 3 → ℝ) :
    f v=f (Pi.single 0 1)*v 0+f (Pi.single 1 1)*v 1+f (Pi.single 2 1)*v 2 := by
  -- The finite expansion avoids any implicit dual-basis convention.
  have he : v=v 0 • Pi.single 0 1+v 1 • Pi.single 1 1+v 2 • Pi.single 2 1 := by
    funext i
    fin_cases i <;> simp
  calc
    f v = f (v 0 • Pi.single 0 1+v 1 • Pi.single 1 1+v 2 • Pi.single 2 1) := congrArg f he
    _ = _ := by rw [map_add,map_add,map_smul,map_smul,map_smul]; ring

/-- Separation of genuine variation coordinates gives all Fritz John signs and slack-mass complementarity.
Use: the subsequent dilation qualification normalizes the objective coefficient to one.
Article: jacobi, Lemma D.3.
Proof: separate the convex variation image from the open improvement cone.
Scaling one strict cone vector to zero fixes the separating level at zero.
Perturb weak cone directions by a vanishing strict vector to read all
coefficient signs, including the zero mass coefficient in the slack case. -/
theorem variation_fritzJohn (active : Prop) {C : Set (Fin 3 → ℝ)}
    (hC : Convex ℝ C) (hzero : 0∈C) (hdis : Disjoint (improvementCone active) C) :
    ∃ a l μ : ℝ,0≤a ∧ 0≤l ∧ 0≤μ ∧ (a≠0 ∨ l≠0 ∨ μ≠0) ∧
      (¬active → l=0) ∧ ∀ v∈C,0≤a*v 0+l*v 1-μ*v 2 := by
  -- A common strict vector exists in both the active and slack cases.
  let w : Fin 3 → ℝ := ![-1,-1,1]
  have hw : w∈improvementCone active := by simp [improvementCone,w]
  obtain ⟨f,u,hleft,hright⟩ := geometric_hahn_banach_open
    (improvementCone_convex active) (improvementCone_open active) hC hdis
  have hu0 : u≤0 := by simpa only [map_zero] using hright 0 hzero
  have hut : ∀ t : ℝ,0<t → f (t • w)<u := by
    intro t ht
    apply hleft
    refine ⟨?_,fun _ => ?_,?_⟩
    · change t*(-1)<0; linarith
    · change t*(-1)<0; linarith
    · change 0<t*1; linarith
  have hu1 : 0≤u := by
    have ht : Tendsto (fun n : ℕ => f ((1/((n:ℝ)+1)) • w)) atTop (𝓝 0) := by
      have hvec : Tendsto (fun n : ℕ => (1/((n:ℝ)+1)) • w) atTop (𝓝 0) := by
        simpa only [zero_smul] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const w
      simpa only [map_zero,Function.comp_def] using f.continuous.tendsto 0 |>.comp hvec
    exact le_of_tendsto ht (Eventually.of_forall fun n => (hut _ (by positivity)).le)
  have hu : u=0 := le_antisymm hu0 hu1
  have hfn : f≠0 := by
    intro hz
    have hh := hleft w hw
    simp only [hz,zero_apply,hu,lt_self_iff_false] at hh
  have hweak (v : Fin 3 → ℝ) (hv0 : v 0≤0) (hv1 : active → v 1≤0) (hv2 : 0≤v 2) : f v≤0 := by
    have ht : Tendsto (fun n : ℕ => f (v+(1/((n:ℝ)+1)) • w)) atTop (𝓝 (f v)) := by
      have hvec : Tendsto (fun n : ℕ => v+(1/((n:ℝ)+1)) • w) atTop (𝓝 v) := by
        simpa only [zero_smul,add_zero] using
          (tendsto_const_nhds (x := v)).add
            ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const w)
      exact f.continuous.tendsto v |>.comp hvec
    apply le_of_tendsto ht
    exact Eventually.of_forall fun n => by
      apply (hleft _ ?_).le.trans_eq hu
      have hn : 0<1/((n:ℝ)+1) := by positivity
      refine ⟨?_,?_,?_⟩
      · change v 0+(1/((n:ℝ)+1))*(-1)<0
        linarith
      · intro hact
        change v 1+(1/((n:ℝ)+1))*(-1)<0
        linarith [hv1 hact]
      · change 0<v 2+(1/((n:ℝ)+1))*1
        linarith
  let a := f (Pi.single 0 1)
  let l := f (Pi.single 1 1)
  let μ := -f (Pi.single 2 1)
  have ha : 0≤a := by
    have h := hweak (-Pi.single 0 1) (by simp) (by intro _; simp) (by simp)
    simpa only [map_neg,neg_nonpos] using h
  have hl : 0≤l := by
    have h := hweak (-Pi.single 1 1) (by simp) (by intro _; simp) (by simp)
    simpa only [map_neg,neg_nonpos] using h
  have hμ : 0≤μ := by
    have h := hweak (Pi.single 2 1) (by simp) (by intro _; simp) (by simp)
    exact neg_nonneg.mpr h
  refine ⟨a,l,μ,ha,hl,hμ,?_,?_,?_⟩
  · by_contra! hz
    apply hfn
    apply ContinuousLinearMap.ext
    intro v
    change f v=0
    rw [functional_three_coordinates]
    have hh : f (Pi.single 2 1)=0 := neg_eq_zero.mp hz.2.2
    have h0 : f (Pi.single 0 1)=0 := hz.1
    have h1 : f (Pi.single 1 1)=0 := hz.2.1
    rw [h0,h1,hh]
    ring
  · intro hslack
    have h := hweak (Pi.single 1 1) (by simp) (by intro h; exact (hslack h).elim) (by simp)
    exact le_antisymm h hl
  · intro v hv
    have h := hright v hv
    rw [hu,functional_three_coordinates] at h
    dsimp only [a,l,μ]
    linarith

end
end jacobi.Variational
