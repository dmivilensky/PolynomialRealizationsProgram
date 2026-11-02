import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Even/odd reflection preserves C2 regularity when the actual value,
first derivative and second derivative satisfy the appropriate midpoint
parity conditions. The gluing uses genuine two-sided derivatives at
the midpoint, formed from the two one-sided original derivatives.
Proposition C.2 applies this elementary lemma to its actual transformed ODE.
Use: the full original target wave is locally this reflection of its genuine transformed solution on each positive strip.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Set Filter
open scoped Topology

/-- Reflection of an actual physical half-domain function with its prescribed scalar parity.
Use: the full original target wave is locally this reflection of its genuine transformed solution on each positive strip.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def reflectMidpoint (ε : ℂ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  if x≤1/2 then f x else ε*f (1-x)

/-- Matching actual midpoint values make the reflected function continuous.
Use: reflection_contDiffOn_two applies this both to the actual reflected slope and to its genuine continuous ODE second derivative.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the elementary continuous gluing lemma, mathlib Continuous.if_le.
Proof: both genuine branches are continuous and their unchanged midpoint values agree. -/
theorem reflectMidpoint_continuous (ε : ℂ) {f : ℝ → ℂ} (hf : Continuous f)
    (hm : f (1/2)=ε*f (1/2)) : Continuous (reflectMidpoint ε f) := by
  apply Continuous.if_le hf (continuous_const.mul (hf.comp (continuous_const.sub continuous_id)))
    continuous_id continuous_const
  intro x hx
  change x=(1/2:ℝ) at hx
  change f x=ε*f (1-x)
  rw [hx,show (1:ℝ)-1/2=1/2 by norm_num]
  exact hm

/-- The actual reflected derivative exists at every point of a symmetric positive strip, including a genuine two-sided derivative at its midpoint.
Use: reflection_contDiffOn_two glues both true derivative levels of the original target waves.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the chain rule and union of one-sided derivatives, mathlib HasDerivWithinAt.union.
Proof: away from the midpoint use the ordinary original branch and reflected chain rules. At the midpoint, the proved original left derivative and reflected right derivative agree by the actual slope parity condition; their union is the genuine full derivative. -/
theorem reflectMidpoint_hasDerivAt {d : ℝ} (hd : d<(1/2:ℝ)) (ε : ℂ) {f g : ℝ → ℂ}
    (hD : ∀ x∈Icc d (1/2),HasDerivWithinAt f (g x) (Icc d (1/2)) x)
    (hf : f (1/2)=ε*f (1/2)) (hg : g (1/2)= -ε*g (1/2))
    {x : ℝ} (hx : x∈Ioo d (1-d)) :
    HasDerivAt (reflectMidpoint ε f) (reflectMidpoint (-ε) g x) x := by
  -- All three locations use the same original derivative, with the midpoint treated by actual one-sided gluing.
  rcases lt_trichotomy x (1/2:ℝ) with hlt|heq|hgt
  · have h := (hD x ⟨hx.1.le,hlt.le⟩).hasDerivAt (Icc_mem_nhds hx.1 hlt)
    have he : reflectMidpoint ε f=ᶠ[𝓝 x] f := by
      filter_upwards [Iio_mem_nhds hlt] with t ht
      exact ite_eq_left ht.le
    simpa only [reflectMidpoint,ite_eq_left hlt.le] using h.congr_of_eventuallyEq he
  · subst x
    have hleft := (hD (1/2) ⟨hd.le,le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hd)
    have hL : HasDerivWithinAt (reflectMidpoint ε f) (g (1/2)) (Iic (1/2:ℝ)) (1/2) :=
      hleft.congr_of_mem (fun _ ht => ite_eq_left ht) (by simp)
    have hi : HasDerivAt (fun t:ℝ => 1-t) (-1:ℝ) (1/2) := by
      simpa only [id_eq] using HasDerivAt.const_sub 1 (hasDerivAt_id (1/2:ℝ))
    have hR0 := (hleft.scomp_of_eq (1/2)
      (hi.hasDerivWithinAt (s := Ici (1/2:ℝ)))
      (show MapsTo (fun t:ℝ => 1-t) (Ici (1/2)) (Iic (1/2)) from fun t ht => by change (1/2:ℝ)≤t at ht; change 1-t≤(1/2:ℝ); linarith)
      (by norm_num : (1/2:ℝ)=1-1/2)).const_mul ε
    have hR : HasDerivWithinAt (fun t => ε*f (1-t)) (g (1/2)) (Ici (1/2:ℝ)) (1/2) := by
      convert hR0 using 1
      · rfl
      · simpa only [zero_sub,neg_one_smul,mul_neg,neg_mul] using hg
    have hEq (t : ℝ) (ht : t∈Ici (1/2:ℝ)) : reflectMidpoint ε f t=ε*f (1-t) := by
      change (1/2:ℝ)≤t at ht
      rcases eq_or_lt_of_le ht with he|hlt
      · subst t
        simpa only [reflectMidpoint,ite_eq_left le_rfl,show (1:ℝ)-1/2=1/2 by norm_num] using hf
      · exact ite_eq_right (not_le_of_gt hlt)
    have hfull := hL.union (hR.congr_of_mem hEq (by simp))
    have hU : Iic (1/2:ℝ)∪Ici (1/2:ℝ)=univ := by ext t; simp only [mem_union,mem_Iic,mem_Ici,mem_univ,iff_true]; exact le_total _ _
    have h := hfull.hasDerivAt (by rw [hU]; exact univ_mem)
    simpa only [reflectMidpoint,ite_eq_left le_rfl] using h
  · have hpoint : 1-x∈Ioo d (1/2) := ⟨by linarith [hx.2],by linarith⟩
    have h := (hD (1-x) ⟨hpoint.1.le,hpoint.2.le⟩).hasDerivAt
      (Icc_mem_nhds hpoint.1 hpoint.2)
    have hi : HasDerivAt (fun t:ℝ => 1-t) (-1:ℝ) x := by
      simpa only [id_eq] using HasDerivAt.const_sub 1 (hasDerivAt_id x)
    have hR := (h.scomp x hi).const_mul ε
    have he : reflectMidpoint ε f=ᶠ[𝓝 x] (fun t => ε*f (1-t)) := by
      filter_upwards [Ioi_mem_nhds hgt] with t ht
      exact ite_eq_right (not_le_of_gt ht)
    have hh := hR.congr_of_eventuallyEq he
    simpa only [reflectMidpoint,ite_eq_right (not_le_of_gt hgt),zero_sub,neg_one_smul,mul_neg,neg_mul] using hh

/-- Matching genuine derivative levels make the reflected original function C2 on the full symmetric positive strip.
Use: the actual transformed ODE and proved exact midpoint Neumann/Dirichlet conditions supply all hypotheses for the original full target eigenfunctions.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: ordinary derivative gluing and the community C2 derivative characterization.
Proof: the preceding true derivative theorem glues f to its reflected slope and glues that slope to its reflected second derivative. The latter is continuous by its proved actual value matching. The community C1 and C2 characterizations then apply on the original open symmetric strip. -/
theorem reflection_contDiffOn_two {d : ℝ} (hd : d<(1/2:ℝ)) (ε : ℂ) {f g h : ℝ → ℂ}
    (hh : Continuous h)
    (hD : ∀ x∈Icc d (1/2),HasDerivWithinAt f (g x) (Icc d (1/2)) x)
    (hDD : ∀ x∈Icc d (1/2),HasDerivWithinAt g (h x) (Icc d (1/2)) x)
    (hf0 : f (1/2)=ε*f (1/2)) (hg0 : g (1/2)= -ε*g (1/2)) (hh0 : h (1/2)=ε*h (1/2)) :
    ContDiffOn ℝ 2 (reflectMidpoint ε f) (Ioo d (1-d)) := by
  -- No second-derivative premise is asserted for the reflected function: both genuine reflected derivative levels are constructed here.
  have hG (x : ℝ) (hx : x∈Ioo d (1-d)) := reflectMidpoint_hasDerivAt hd ε hD hf0 hg0 hx
  have hH (x : ℝ) (hx : x∈Ioo d (1-d)) :
      HasDerivAt (reflectMidpoint (-ε) g) (reflectMidpoint ε h x) x := by
    simpa only [neg_neg] using reflectMidpoint_hasDerivAt hd (-ε) hDD hg0 (by simpa only [neg_neg] using hh0) hx
  have hG1 : ContDiffOn ℝ 1 (reflectMidpoint (-ε) g) (Ioo d (1-d)) := by
    apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).mpr
    refine ⟨fun x hx => (hH x hx).differentiableAt.differentiableWithinAt,?_⟩
    exact (reflectMidpoint_continuous ε hh hh0).continuousOn.congr (fun x hx => by
      exact (hH x hx).hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffOn x hx))
  apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioo).mpr
  refine ⟨fun x hx => (hG x hx).differentiableAt.differentiableWithinAt,by norm_num,?_⟩
  exact hG1.congr (fun x hx => (hG x hx).deriv)

end
end jacobi.GelfandLevitan
