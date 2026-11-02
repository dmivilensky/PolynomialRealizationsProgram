import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
Article: jacobi, Theorem 2.1.
An elementary oscillation argument excludes an eventually positive solution
of u'' <= -c*u for a fixed positive c. This is the comparison step used for
the actual Liouville-transformed Bessel equation in Wave.
Source: the classical concavity proof of Sturm oscillation.
Use: proves actual Bessel oscillation after the Liouville transformation.
-/
namespace jacobi.Bessel
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

/-- A function with a uniformly negative restoring curvature cannot stay positive on a half-line.
Use: proves actual Bessel oscillation after the Liouville transformation.
Article: jacobi, Theorem 2.1.
Proof: the slope decreases. A negative slope would force the positive
function below zero by the mean value theorem, so all slopes must be
nonnegative. The function then stays above its positive initial height;
its second derivative is bounded by a fixed negative constant, forcing
its slope below zero after a finite distance. -/
theorem not_positive_restoring {f g h : ℝ → ℝ} {R c : ℝ} (hc : 0<c)
    (hf : ∀ x∈Ici R,HasDerivAt f (g x) x)
    (hg : ∀ x∈Ici R,HasDerivAt g (h x) x)
    (hh : ∀ x∈Ici R,h x≤-c*f x) : ¬∀ x∈Ici R,0<f x := by
  -- Decreasing slopes cannot be negative while the original function stays positive forever.
  intro hp
  have hfc : ContinuousOn f (Ici R) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Ici R) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hfd : DifferentiableOn ℝ f (interior (Ici R)) :=
    fun x hx => (hf x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hgd : DifferentiableOn ℝ g (interior (Ici R)) :=
    fun x hx => (hg x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hanti : AntitoneOn g (Ici R) := antitoneOn_of_deriv_nonpos (convex_Ici R) hgc hgd (by
    intro x hx
    rw [(hg x (interior_subset hx)).deriv]
    exact (hh x (interior_subset hx)).trans (by nlinarith [hp x (interior_subset hx)]))
  have hnonneg : ∀ x∈Ici R,0≤g x := by
    intro x hx
    by_contra hn
    have hn : g x<0 := lt_of_not_ge hn
    let y := x+(f x+1)/(-g x)
    have hd : 0<(f x+1)/(-g x) := div_pos (by linarith [hp x hx]) (neg_pos.mpr hn)
    have hxy : x≤y := by dsimp [y]; linarith
    have hb := (convex_Ici x).image_sub_le_mul_sub_of_deriv_le
      (hfc.mono (Ici_subset_Ici.mpr hx))
      (fun t ht => (hf t (le_trans hx (interior_subset ht))).differentiableAt.differentiableWithinAt)
      (C := g x) (by
        intro t ht
        rw [(hf t (le_trans hx (interior_subset ht))).deriv]
        exact hanti hx (le_trans hx (interior_subset ht)) (interior_subset ht))
      x (by simp) y hxy hxy
    have he : g x*(y-x)=-(f x+1) := by
      dsimp [y]
      field_simp [hn.ne]
      ring
    rw [he] at hb
    linarith [hp y (le_trans hx hxy)]
  -- A nondecreasing positive function has uniformly negative second derivative.
  have hmono : MonotoneOn f (Ici R) := monotoneOn_of_deriv_nonneg (convex_Ici R) hfc hfd (by
    intro x hx
    rw [(hf x (interior_subset hx)).deriv]
    exact hnonneg x (interior_subset hx))
  have hpos : 0<c*f R := mul_pos hc (hp R (by simp))
  let y := R+(g R+1)/(c*f R)
  have hRy : R≤y := by
    dsimp [y]
    linarith [div_pos (show 0<g R+1 by linarith [hnonneg R (by simp)]) hpos]
  have hb := (convex_Ici R).image_sub_le_mul_sub_of_deriv_le hgc hgd
    (C := -c*f R) (by
      intro x hx
      rw [(hg x (interior_subset hx)).deriv]
      exact (hh x (interior_subset hx)).trans
        (mul_le_mul_of_nonpos_left (hmono (by simp) (interior_subset hx) (interior_subset hx)) (neg_nonpos.mpr hc.le)))
    R (by simp) y hRy hRy
  have he : (-c*f R)*(y-R)=-(g R+1) := by
    dsimp [y]
    field_simp [hc.ne',(hp R (by simp)).ne']
    ring
  rw [he] at hb
  linarith [hnonneg y hRy]

/-- A continuous zero-free real function keeps its positive initial sign on a half-line.
Use: supplies the sign needed by the restoring-curvature argument.
Article: jacobi, Theorem 2.1.
Proof: an opposite sign at any later point would give a zero on the
compact joining interval by the intermediate value theorem. -/
theorem positive_on_Ici_of_no_zero {f : ℝ → ℝ} {R : ℝ}
    (hf : ContinuousOn f (Ici R)) (hne : ∀ x∈Ici R,f x≠0) (hp : 0<f R) :
    ∀ x∈Ici R,0<f x := by
  -- The sign is determined on each finite segment; no limit at infinity is assumed.
  intro x hx
  by_contra hn
  obtain ⟨y,hy,he⟩ := intermediate_value_Icc' hx (hf.mono (Icc_subset_Ici_self))
    (show (0:ℝ)∈Icc (f x) (f R) from ⟨le_of_not_gt hn,hp.le⟩)
  exact hne y hy.1 he

/-- A restoring equation with a uniformly positive coefficient has a zero on every sufficiently placed half-line.
Use: proves infinitely many genuine Bessel zeros without a borrowed asymptotic zero list.
Article: jacobi, Theorem 2.1.
Proof: without a zero continuity fixes the sign. In either sign, apply
the proved restoring-curvature contradiction to the positive solution
or its negative. Every ordinary derivative is supplied explicitly. -/
theorem restoring_has_zero {f g h q : ℝ → ℝ} {R c : ℝ} (hc : 0<c)
    (hf : ∀ x∈Ici R,HasDerivAt f (g x) x)
    (hg : ∀ x∈Ici R,HasDerivAt g (h x) x)
    (he : ∀ x∈Ici R,h x+q x*f x=0)
    (hq : ∀ x∈Ici R,c≤q x) : ∃ x∈Ici R,f x=0 := by
  -- A zero-free solution has a single sign on the entire connected half-line.
  by_contra hn
  have hne : ∀ x∈Ici R,f x≠0 := by simpa only [not_exists,not_and] using hn
  have hfc : ContinuousOn f (Ici R) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  by_cases hp : 0<f R
  · have hpos := positive_on_Ici_of_no_zero hfc hne hp
    apply not_positive_restoring hc hf hg ?_ hpos
    intro x hx
    nlinarith [he x hx,mul_le_mul_of_nonneg_right (hq x hx) (hpos x hx).le]
  · have hp : 0< -f R := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) (hne R (by simp)))
    have hpos := positive_on_Ici_of_no_zero hfc.neg (by
      intro x hx
      exact neg_ne_zero.mpr (hne x hx)) hp
    apply not_positive_restoring (f := fun x => -f x) (g := fun x => -g x)
      (h := fun x => -h x) hc (fun x hx => (hf x hx).neg) (fun x hx => (hg x hx).neg) ?_ hpos
    intro x hx
    have hxneg : 0< -f x := hpos x hx
    nlinarith [he x hx,mul_le_mul_of_nonneg_right (hq x hx) hxneg.le]

end
end jacobi.Bessel
