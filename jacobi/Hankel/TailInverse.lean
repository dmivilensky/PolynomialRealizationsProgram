import jacobi.Hankel.JostInverse
import jacobi.Hankel.RayBound

/-!
Article: jacobi, Lemma E.1.
Its genuine future supremum is finite, so absorption retains the
spatial decay of an actual forcing term. This is the estimate needed
to prove the cubic complex Jost remainder from its literal residual.
Use: tailInverse_bound absorbs the true Volterra tail without weakening a cubic forcing estimate to the fixed cutoff bound.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

/-- The actual supremum of the amplitude norm on the closed future ray.
Use: tailInverse_bound absorbs the true Volterra tail without weakening a cubic forcing estimate to the fixed cutoff bound.
Article: jacobi, Lemma E.1.
-/
def tailNorm (f : OutgoingSpace) (x : ℝ) : ℝ := sSup ((fun y => ‖f y‖) '' Ici x)

/-- The set defining the original future supremum is nonempty and bounded above by the genuine Banach norm.
Use: all subsequent supremum manipulations concern the actual bounded continuous amplitude.
Article: jacobi, Lemma E.1.
Proof: the starting point belongs to its own closed ray, and point evaluation is bounded by the genuine bounded-continuous norm. -/
theorem tailNorm_set_bounds (f : OutgoingSpace) (x : ℝ) :
    ((fun y => ‖f y‖) '' Ici x).Nonempty ∧ BddAbove ((fun y => ‖f y‖) '' Ici x) :=
  ⟨⟨‖f x‖,⟨x,Set.self_mem_Ici,rfl⟩⟩,⟨‖f‖,by rintro _ ⟨y,_,rfl⟩; exact f.norm_coe_le_norm y⟩⟩

/-- Every value on the actual future ray is bounded by its genuine supremum.
Use: the original kernel's causal support permits outgoingIntegral_ray_bound to use this same local supremum.
Article: jacobi, Lemma E.1.
Proof: apply the least-upper-bound inequality to the original point in the bounded image of the closed ray. -/
theorem norm_le_tailNorm (f : OutgoingSpace) {x y : ℝ} (hxy : x≤y) :
    ‖f y‖≤tailNorm f x :=
  le_csSup (tailNorm_set_bounds f x).2 ⟨y,hxy,rfl⟩

/-- The genuine future amplitude supremum is nonnegative.
Use: tailInverse_bound absorbs an actual nonnegative local norm in its half-contraction inequality.
Article: jacobi, Lemma E.1.
Proof: bound the nonnegative amplitude norm at the starting point by the true supremum. -/
theorem tailNorm_nonneg (f : OutgoingSpace) (x : ℝ) : 0≤tailNorm f x :=
  (norm_nonneg _).trans (norm_le_tailNorm f le_rfl)

/-- The actual inverse-square Volterra equation preserves every proved bound on its true future forcing under a local half-contraction.
Use: a cubic actual residual gives a cubic Jost error on the common complex-order domain, without an assumed asymptotic certificate.
Article: jacobi, Lemma E.1.
Proof: use the genuine causal kernel bound on each later ray, take the actual bounded supremum, and absorb |c|/x times that supremum. -/
theorem tailInverse_bound {R x G : ℝ} (hR : 0<R) (hx : R≤x)
    {c : ℂ} (hc : ‖c‖/x≤1/2) (f : OutgoingSpace)
    (hf : ∀ y : ℝ,x≤y → ‖f y+c*outgoingIntegral (inverseSquare R) f y‖≤G) :
    tailNorm f x≤2*G := by
  -- The supremum is taken only after the true causal support has supplied the sharper later-ray mass.
  have hxp : 0<x := hR.trans_le hx
  have hM := tailNorm_nonneg f x
  have hb (y : ℝ) (hy : x≤y) : ‖f y‖≤G+(‖c‖/x)*tailNorm f x := by
    have ht := outgoingIntegral_ray_bound hR (hx.trans hy) hM f
      (fun z hz => norm_le_tailNorm f (hy.trans hz.le))
    have hd : tailNorm f x/y≤tailNorm f x/x :=
      div_le_div_of_nonneg_left hM hxp hy
    calc
      ‖f y‖ = ‖(f y+c*outgoingIntegral (inverseSquare R) f y)-c*outgoingIntegral (inverseSquare R) f y‖ := by congr 1; ring
      _ ≤ ‖f y+c*outgoingIntegral (inverseSquare R) f y‖+‖c*outgoingIntegral (inverseSquare R) f y‖ := norm_sub_le _ _
      _ ≤ G+‖c‖*(tailNorm f x/x) := by
        rw [norm_mul]
        exact add_le_add (hf y hy) (mul_le_mul_of_nonneg_left (ht.trans hd) (norm_nonneg c))
      _ = _ := by ring
  have hs : tailNorm f x≤G+(‖c‖/x)*tailNorm f x :=
    csSup_le (tailNorm_set_bounds f x).1 (by rintro _ ⟨y,hy,rfl⟩; exact hb y hy)
  nlinarith [mul_le_mul_of_nonneg_right hc hM]

end
end jacobi.Hankel
