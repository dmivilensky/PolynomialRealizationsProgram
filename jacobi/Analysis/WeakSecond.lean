import jacobi.Analysis.CompactTest
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: jacobi, Proposition 2.2.
The one-dimensional weak second derivative determines a continuous function
up to an affine function. The proof uses mathlib's smooth approximate identity.
Source: elementary one-dimensional distribution theory, proved here with C2 tests.
Use: weak_second_zero_affine identifies a continuous Green column with its
twice-integrated forcing, fixing its classical derivatives without any
classification at the singular endpoints.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter Function MeasureTheory ContinuousLinearMap Metric
open scoped Topology Convolution

/-- A reflected translate has the unchanged second derivative of its original function.
Use: mollified_second_zero inserts reflected smooth bumps into the actual
compact-test Green identity.
Article: jacobi, Proposition 2.2.
Proof: the first reflection contributes a minus sign; differentiating once
more cancels the second reflection's minus sign. -/
theorem deriv_twice_reflect (f : ℝ → ℝ) (x y : ℝ) :
    deriv (deriv (fun s => f (x-s))) y=deriv (deriv f) (x-y) := by
  have he : deriv (fun s => f (x-s))=fun s => -deriv f (x-s) :=
    funext (fun s => deriv_comp_const_sub f x s)
  rw [he]
  change deriv (-(fun s => deriv f (x-s))) y=_
  rw [deriv.neg,deriv_comp_const_sub,neg_neg]

/-- A compact smooth convolution of a weakly affine function has zero
ordinary second derivative on every interval away from the support boundary.
Use: weak_second_zero_affine takes the shrinking-bump limit of its exact
affine three-point identity.
Article: jacobi, Proposition 2.2.
Proof: both actual convolution derivatives differentiate the compact bump.
The reflected bump is an admissible compact C2 test, so its pairing vanishes. -/
theorem mollified_second_zero {f B : ℝ → ℝ} {a b l r ε : ℝ}
    (hf : Continuous f) (hB : ContDiff ℝ 2 B) (hc : HasCompactSupport B)
    (hs : tsupport B ⊆ closedBall 0 ε) (hl : a+ε≤l) (hr : r≤b-ε)
    (hw : ∀ q : ℝ → ℝ, ContDiff ℝ 2 q → HasCompactSupport q →
      tsupport q ⊆ Ioo a b → (∫ s : ℝ,f s*deriv (deriv q) s)=0)
    {x : ℝ} (hx : x∈Ioo l r) :
    deriv (deriv (B ⋆[lsmul ℝ ℝ,volume] f)) x=0 := by
  have hB1 : ContDiff ℝ 1 B := hB.of_le (by norm_num)
  have hBd : ContDiff ℝ 1 (deriv B) := (show ContDiff ℝ (1+1) B from hB).deriv'
  have hd1 : deriv (B ⋆[lsmul ℝ ℝ,volume] f)=
      (deriv B ⋆[lsmul ℝ ℝ,volume] f) :=
    funext (fun y => (hc.hasDerivAt_convolution_left (lsmul ℝ ℝ)
      hB1 hf.locallyIntegrable y).deriv)
  rw [hd1,(hc.deriv.hasDerivAt_convolution_left (lsmul ℝ ℝ)
    hBd hf.locallyIntegrable x).deriv,convolution_eq_swap]
  let q := fun s => B (x-s)
  have hqc : HasCompactSupport q := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hqs : tsupport q ⊆ Ioo a b := by
    intro s hs'
    have he : tsupport q=(Homeomorph.subLeft x) ⁻¹' tsupport B :=
      tsupport_comp_eq_preimage B (Homeomorph.subLeft x)
    rw [he] at hs'
    have hnorm := hs hs'
    have habs : |x-s|≤ε := by
      rw [mem_closedBall] at hnorm
      change dist (x-s) 0≤ε at hnorm
      simpa only [Real.dist_eq,sub_zero] using hnorm
    constructor <;> linarith [(abs_le.mp habs).1,(abs_le.mp habs).2,hx.1,hx.2]
  have hh := hw q (hB.comp (contDiff_const.sub contDiff_id)) hqc hqs
  simpa only [q,lsmul_apply,smul_eq_mul,deriv_twice_reflect,mul_comm] using hh

/-- A C2 function with zero second derivative satisfies the affine three-point identity.
Use: weak_second_zero_affine passes this exact polynomial identity to the
continuous limit, avoiding convergence assumptions on derivatives.
Article: jacobi, Proposition 2.2.
Source: the mean value theorem, applied twice.
Proof: the first derivative is constant on the connected open interval;
subtract its linear primitive and apply the same theorem once more. -/
theorem second_zero_threepoint {f : ℝ → ℝ} {a b p q x : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioo a b))
    (hz : ∀ t∈Ioo a b,deriv (deriv f) t=0)
    (hp : p∈Ioo a b) (hq : q∈Ioo a b) (hx : x∈Ioo a b) :
    (q-p)*(f x-f p)=(x-p)*(f q-f p) := by
  have hfd : ContDiffOn ℝ 1 (deriv f) (Ioo a b) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have he (t : ℝ) (ht : t∈Ioo a b) : deriv f t=deriv f p :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (hfd.differentiableOn (by norm_num)) (fun _ ht => hz _ ht) ht hp
  have hdiff (t : ℝ) (ht : t∈Ioo a b) :
      HasDerivAt (fun s => f s-deriv f p*s) 0 t := by
    have hd := ((hf t ht).contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by norm_num)
    convert hd.hasDerivAt.sub ((hasDerivAt_id t).const_mul (deriv f p)) using 1
    · rfl
    · rw [he t ht]
      ring
  have hc (t : ℝ) (ht : t∈Ioo a b) : f t-deriv f p*t=f p-deriv f p*p :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun s hs => (hdiff s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hdiff s hs).deriv) ht hp
  have hxx : f x=f p+deriv f p*(x-p) := by linarith [hc x hx]
  have hqq : f q=f p+deriv f p*(q-p) := by linarith [hc q hq]
  rw [hxx,hqq]
  ring

/-- A continuous weakly affine function satisfies the same exact three-point
identity as a classical affine function.
Use: weak_second_zero_affine fixes its two coefficients from interior values.
Article: jacobi, Proposition 2.2.
Source: smoothing by a compact approximate identity.
Proof: choose bumps whose supports fit around all three fixed points. Their
convolutions have zero second derivative and hence the exact affine identity.
Mathlib's approximate-identity theorem passes that identity to the limit. -/
theorem weak_second_zero_threepoint {f : ℝ → ℝ} {a b p q x : ℝ}
    (hf : Continuous f)
    (hw : ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b → (∫ s : ℝ,f s*deriv (deriv g) s)=0)
    (hp : p∈Ioo a b) (hq : q∈Ioo a b) (hx : x∈Ioo a b) :
    (q-p)*(f x-f p)=(x-p)*(f q-f p) := by
  -- One positive margin fits all three points and every shrinking bump.
  let L := min p (min q x)
  let R := max p (max q x)
  have hL : a<L := lt_min hp.1 (lt_min hq.1 hx.1)
  have hR : R<b := max_lt hp.2 (max_lt hq.2 hx.2)
  let δ := min (L-a) (b-R)/2
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδL : δ<L-a := by
    have hh := min_le_left (L-a) (b-R)
    dsimp [δ]
    linarith
  have hδR : δ<b-R := by
    have hh := min_le_right (L-a) (b-R)
    dsimp [δ]
    linarith
  have hp' : p∈Ioo (a+δ) (b-δ) := by
    constructor <;> linarith [min_le_left p (min q x),le_max_left p (max q x)]
  have hq' : q∈Ioo (a+δ) (b-δ) := by
    constructor <;> linarith [(min_le_right p (min q x)).trans (min_le_left q x),
      (le_max_left q x).trans (le_max_right p (max q x))]
  have hx' : x∈Ioo (a+δ) (b-δ) := by
    constructor <;> linarith [(min_le_right p (min q x)).trans (min_le_right q x),
      (le_max_right q x).trans (le_max_right p (max q x))]
  let φ : ℕ → ContDiffBump (0:ℝ) := fun n =>
    ⟨δ/(2*((n:ℝ)+1)),δ/((n:ℝ)+1),by positivity,by
      apply div_lt_div_of_pos_left hδ (by positivity)
      nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]⟩
  let F := fun n => ((φ n).normed volume ⋆[lsmul ℝ ℝ,volume] f)
  have hε (n : ℕ) : (φ n).rOut≤δ := by
    change δ/((n:ℝ)+1)≤δ
    exact div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0:ℝ)≤n)])
  have he (n : ℕ) : (q-p)*(F n x-F n p)=(x-p)*(F n q-F n p) := by
    have hc := (φ n).hasCompactSupport_normed (μ := volume)
    have hd : ContDiff ℝ 2 ((φ n).normed volume) := (φ n).contDiff_normed
    have hs : tsupport ((φ n).normed volume) ⊆ closedBall 0 (φ n).rOut :=
      ((φ n).tsupport_normed_eq (μ := volume)).subset
    apply second_zero_threepoint
      (hc.contDiff_convolution_left (lsmul ℝ ℝ) hd hf.locallyIntegrable).contDiffOn _ hp' hq' hx'
    intro t ht
    exact mollified_second_zero hf hd hc hs (by linarith [hε n])
      (by linarith [hε n]) hw ht
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
    simpa only [mul_zero,φ,mul_one_div] using hh
  -- Pass an identity involving only values to the limit. No convergence
  -- of the mollified first or second derivatives is needed.
  have hlim (t : ℝ) : Tendsto (fun n => F n t) atTop (𝓝 (f t)) :=
    ContDiffBump.convolution_tendsto_right_of_continuous hφ hf t
  exact tendsto_nhds_unique (((hlim x).sub (hlim p)).const_mul (q-p))
    ((((hlim q).sub (hlim p)).const_mul (x-p)).congr (fun n => (he n).symm))

/-- A continuous function with zero weak second derivative on an open
interval is the restriction of an actual affine function.
Use: local primitives of the Green forcing have this affine difference
from the original continuous Green column, hence supply its true derivatives.
Article: jacobi, Proposition 2.2.
Source: the elementary one-dimensional distributional affine lemma.
Proof: the exact three-point identity determines the function everywhere
from two distinct interior values. -/
theorem weak_second_zero_affine {f : ℝ → ℝ} {a b : ℝ}
    (hab : a<b) (hf : Continuous f)
    (hw : ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b → (∫ s : ℝ,f s*deriv (deriv g) s)=0) :
    ∃ A B : ℝ,∀ x∈Ioo a b,f x=A*x+B := by
  let p := (2*a+b)/3
  let q := (a+2*b)/3
  have hp : p∈Ioo a b := by dsimp [p]; constructor <;> linarith
  have hq : q∈Ioo a b := by dsimp [q]; constructor <;> linarith
  have hqp : q-p≠0 := by dsimp [p,q]; linarith
  refine ⟨(f q-f p)/(q-p),f p-(f q-f p)/(q-p)*p,fun x hx => ?_⟩
  have he := weak_second_zero_threepoint hf hw hp hq hx
  field_simp [hqp]
  nlinarith

end
end jacobi.Analysis
