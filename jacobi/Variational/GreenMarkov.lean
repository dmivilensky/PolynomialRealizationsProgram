import jacobi.Variational.FredholmGreen
import jacobi.Continuum.DirichletSplit

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The actual coercive differential form separates across a zero Dirichlet
value. Hence a Green-vector combination whose sources are left of that
point vanishes identically on the right. This gives the exact interval
factorization G(x,z)=G(x,a)*G(a,z)/G(a,a), without presupposing Jost solutions.
Source: orthogonal H1 half-line splitting and the proved actual coercivity.
Use: isolates the energy of the right component in the coercive Green factorization argument.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Set Filter jacobi.Continuum
open chebyshev2.Continuum chebyshev2.Sobolev
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The genuine Schrödinger form pairs the two zero-boundary half-line components to zero.
Use: isolates the energy of the right component in the coercive Green factorization argument.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: the H1 inner product vanishes by coordinate restriction, and the
physical representatives have disjoint supports, so the density integral also vanishes. -/
theorem L1Source.dirichlet_form_cross (m : L1Source) (s a : ℝ) (u : H1) (hu : H1.rep u a=0) :
    inner ℝ (m.fredholmPencil s (h1LeftCut a u)) (u-h1LeftCut a u)=0 := by
  -- Both the Sobolev and potential terms split at a genuine zero boundary value.
  change inner ℝ (h1LeftCut a u-s • densityOperator m.value (h1LeftCut a u)) (u-h1LeftCut a u)=0
  rw [inner_sub_left,real_inner_smul_left,h1DirichletSplit_inner,
    real_inner_comm (u-h1LeftCut a u) (densityOperator m.value (h1LeftCut a u)),
    sobolevDensityOperator_form m.integrable]
  have hz : (fun x => m.value x*H1.rep (u-h1LeftCut a u) x*H1.rep (h1LeftCut a u) x)=0 := by
    funext x
    by_cases hx : x≤a
    · rw [h1RightCut_rep_left a u hx,mul_zero,zero_mul]
      rfl
    · rw [h1LeftCut_rep_right a u hu (le_of_not_ge hx),mul_zero]
      rfl
  rw [hz]
  simp only [integral_zero',mul_zero,sub_zero]

/-- A zero-boundary H1 solution with no right-half-line forcing vanishes identically on that half-line.
Use: applies to the difference of two actual Green columns whose boundary values have been matched.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: test with the actual right Dirichlet component. Cross terms vanish;
the strictly positive spectral-margin coercivity forces this component to
be zero. Its physical representative equals the original one on the right. -/
theorem L1Source.dirichlet_right_unique (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) (a : ℝ) (u : H1) (hu : H1.rep u a=0)
    (hforce : ∀ w : H1,(∀ x,x≤a → H1.rep w x=0) → inner ℝ (m.fredholmPencil s u) w=0) :
    ∀ x,a≤x → H1.rep u x=0 := by
  -- The right test is an actual H1 vector supplied by the proved coordinate split.
  let w := u-h1LeftCut a u
  have hw := hforce w (fun x hx => h1RightCut_rep_left a u hx)
  have hdecomp : u=h1LeftCut a u+w := by dsimp only [w]; abel
  have hcross := m.dirichlet_form_cross s a u hu
  rw [hdecomp,map_add,inner_add_left,hcross,zero_add] at hw
  have hb := m.fredholmPencil_coercive hs w
  have hnorm : ‖w‖=0 := by
    rw [hw] at hb
    have hc : 0<1-s*observe m .top := sub_pos.mpr hp
    have hz : ‖w‖^2=0 := le_antisymm (by nlinarith : ‖w‖^2≤0) (sq_nonneg _)
    nlinarith [norm_nonneg w]
  have hwzero : w=0 := norm_eq_zero.mp hnorm
  intro x hx
  have hr := h1RightCut_rep_right a u hu hx
  change H1.rep w x=H1.rep u x at hr
  rw [hwzero,H1.rep_zero] at hr
  exact hr.symm

/-- The genuine Green kernel factors exactly across every intermediate point.
Use: constructs global positive homogeneous solutions and the actual Green diagonal differential identity.
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: match the intermediate boundary value by subtracting a multiple of
its actual Green column. All forcing evaluations lie on the left. The proved
Dirichlet uniqueness makes the difference vanish on the entire right half-line. -/
theorem L1Source.fredholmGreen_markov (m : L1Source) {s : ℝ} (hs : 0≤s)
    (hp : s*observe m .top<1) {x a z : ℝ} (hxa : x≤a) (haz : a≤z) :
    m.fredholmGreen s hs hp x z=
      (m.fredholmGreen s hs hp x a/m.fredholmGreen s hs hp a a)*m.fredholmGreen s hs hp a z := by
  -- Strict diagonal positivity makes matching the two actual Green columns legitimate.
  let G := m.fredholmGreen s hs hp
  let c := G x a/G a a
  let u := m.fredholmGreenVector s hs hp x-c • m.fredholmGreenVector s hs hp a
  have hdiag : 0<G a a := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (m.fredholmGreen_diagonal hs hp a).1
  have hrep (y : ℝ) : H1.rep u y=G x y-c*G a y := by
    rw [h1Rep_sub,H1.rep_smul]
    dsimp only
    rw [m.fredholmGreenVector_rep hs hp,m.fredholmGreenVector_rep hs hp]
  have hu : H1.rep u a=0 := by
    rw [hrep]
    dsimp only [c]
    rw [div_mul_cancel₀ _ hdiag.ne',sub_self]
  have hforce (w : H1) (hw : ∀ y,y≤a → H1.rep w y=0) : inner ℝ (m.fredholmPencil s u) w=0 := by
    change inner ℝ (m.fredholmPencil s
      (m.fredholmGreenVector s hs hp x-c • m.fredholmGreenVector s hs hp a)) w=0
    rw [map_sub,map_smul,inner_sub_left,real_inner_smul_left,
      m.fredholmGreen_identity hs hp,m.fredholmGreen_identity hs hp,hw x hxa,hw a le_rfl,mul_zero,sub_self]
  have hz := m.dirichlet_right_unique hs hp a u hu hforce z haz
  rw [hrep] at hz
  change G x z=c*G a z
  linarith

end
end jacobi.Variational
