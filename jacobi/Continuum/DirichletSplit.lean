import chebyshev2.Sobolev.Operators

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
In the existing integrating-factor realization of H1, truncating the L2
coordinate to a left half-line gives a genuine H1 vector. If the original
continuous representative vanishes at the cutting point, this is exactly
its zero extension from the left; the complementary vector is the right
zero extension. Their H1 inner product and density pairings vanish.
Source: the causal H1 representation already proved in chebyshev2.
Use: evaluates complementary Dirichlet vectors and Green-vector linear combinations.
-/
namespace jacobi.Continuum
noncomputable section
open MeasureTheory Real Set Filter chebyshev2.Continuum chebyshev2.Sobolev
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Evaluation of a genuine H1 difference is the pointwise difference of its continuous representatives.
Use: evaluates complementary Dirichlet vectors and Green-vector linear combinations.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: apply the reproducing identity and linearity in the second inner-product argument. -/
theorem h1Rep_sub (u v : H1) (x : ℝ) : H1.rep (u-v) x=H1.rep u x-H1.rep v x := by
  rw [← H1.reproducing,inner_sub_right,H1.reproducing,H1.reproducing]

/-- The left half-line restriction in the actual L2 coordinates of H1.
Use: creates genuine zero-extended Dirichlet test vectors for the Green kernel's interval factorization.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
-/
def h1LeftCut (a : ℝ) (u : H1) : H1 :=
  ((Lp.memLp u).indicator measurableSet_Iic).toLp ((Iic a).indicator (fun x => u x))

/-- The actual L2 representative of the left cut agrees a.e. with the literal half-line indicator.
Use: identifies both the causal integral and orthogonal split with actual H1 vectors.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: use the canonical a.e. representative theorem for the constructed Lp element. -/
theorem h1LeftCut_coe (a : ℝ) (u : H1) :
    (h1LeftCut a u : ℝ → ℝ)=ᵐ[volume] (Iic a).indicator (fun x => u x) :=
  MemLp.coeFn_toLp _

/-- The physical representative of the left cut is its exact causal integral up to min(x,a).
Use: a zero Dirichlet value eliminates the exponential continuation beyond the cut.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: substitute the indicator a.e. into the causal head integral and intersect the two left half-lines. -/
theorem h1LeftCut_head (a : ℝ) (u : H1) (x : ℝ) :
    H1.rep (h1LeftCut a u) x=exp (-x)*(∫ y in Iic (min x a),exp y*u y) := by
  rw [H1.rep,causalValue_head]
  congr 1
  have he : (fun y => exp y*h1LeftCut a u y)=ᵐ[volume]
      (Iic a).indicator (fun y => exp y*u y) := by
    filter_upwards [h1LeftCut_coe a u] with y hy
    rw [hy]
    by_cases hya : y≤a <;> simp [hya]
  rw [integral_congr_ae (ae_restrict_of_ae he),setIntegral_indicator measurableSet_Iic,Iic_inter_Iic]

/-- A left cut agrees exactly with the original physical H1 representative before the cut.
Use: the right complementary Dirichlet vector vanishes on that half-line.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the causal head integral depends only on coordinates to the left of its evaluation point. -/
theorem h1LeftCut_rep_left (a : ℝ) (u : H1) {x : ℝ} (hx : x≤a) :
    H1.rep (h1LeftCut a u) x=H1.rep u x := by
  rw [h1LeftCut_head,min_eq_left hx,H1.rep,causalValue_head]

/-- A zero Dirichlet boundary value makes the actual left cut vanish identically to its right.
Use: removes the left component from a right half-line Green test.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the causal continuation equals exp(-x)*exp(a)*u(a), which vanishes. -/
theorem h1LeftCut_rep_right (a : ℝ) (u : H1) (hu : H1.rep u a=0) {x : ℝ} (hx : a≤x) :
    H1.rep (h1LeftCut a u) x=0 := by
  rw [h1LeftCut_head,min_eq_right hx]
  have hh := causalValue_head_mul u a
  change exp a*H1.rep u a=(∫ y in Iic a,exp y*u y) at hh
  rw [← hh,hu,mul_zero,mul_zero]

/-- The actual right complementary Dirichlet vector vanishes on the left half-line.
Use: all Green evaluation functionals on the left annihilate this right test vector.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: subtract the already proved identical left representatives. -/
theorem h1RightCut_rep_left (a : ℝ) (u : H1) {x : ℝ} (hx : x≤a) :
    H1.rep (u-h1LeftCut a u) x=0 := by
  rw [h1Rep_sub,h1LeftCut_rep_left a u hx,sub_self]

/-- The actual right complementary Dirichlet vector equals the original representative on the right.
Use: identifies the original Green combination from its right-component vanishing.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: subtract the proved zero left continuation after the cutting point. -/
theorem h1RightCut_rep_right (a : ℝ) (u : H1) (hu : H1.rep u a=0) {x : ℝ} (hx : a≤x) :
    H1.rep (u-h1LeftCut a u) x=H1.rep u x := by
  rw [h1Rep_sub,h1LeftCut_rep_right a u hu hx,sub_zero]

/-- The left and right L2 coordinate restrictions are orthogonal in the genuine H1 inner product.
Use: the coercive Green form separates at every zero Dirichlet boundary value.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: their canonical L2 representatives are complementary indicators,
so their pointwise product vanishes a.e. before integrating the H1 inner product. -/
theorem h1DirichletSplit_inner (a : ℝ) (u : H1) :
    inner ℝ (h1LeftCut a u) (u-h1LeftCut a u)=0 := by
  -- Orthogonality is computed in the actual L2 coordinates defining H1.
  rw [L2.inner_def]
  have he : (fun x => inner ℝ (h1LeftCut a u x) ((u-h1LeftCut a u) x))=ᵐ[volume] 0 := by
    filter_upwards [h1LeftCut_coe a u,Lp.coeFn_sub u (h1LeftCut a u)] with x hx hsub
    rw [hsub]
    dsimp only [Pi.sub_apply]
    rw [hx]
    by_cases hxa : x≤a <;> simp [hxa]
  simpa only [Pi.zero_apply,integral_zero] using integral_congr_ae he

end
end jacobi.Continuum
