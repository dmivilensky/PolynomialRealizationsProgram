import polyak.General.Cubic
import polyak.General.Regions.Quadratics

/-! Article: Appendix D, Lemma Kmu and Corollary C(c).
The two source quotients are literal polynomials, with endpoint and factor
identities checked independently of any numerical evaluation.
-/
namespace polyak.General.Regions
noncomputable section

/-- The source convex quotient at a positive dominant root. -/
def Kmu (q : Tuning) (r c : ℝ) : ℝ :=
  4*q.beta*r^3*c^2 +
  2*r*(r^3*(q.y-1)-q.beta*r^3+q.beta*r^2-2*q.beta*r-q.beta^2)*c +
  r^5+r^4*q.y-r^3*q.y+r^3-q.beta*r^4+q.beta*r^3-q.beta*r^2*q.y-
    q.beta*r^2-q.beta*r*q.y+q.beta*r+q.beta^2*r^2+q.beta^2

/-- The source concave quotient at a negative dominant root. -/
def KL (q : Tuning) (r c : ℝ) : ℝ :=
  -4*q.beta*r^3*c^2 +
  2*r^2*(q.beta^2+3*q.beta+q.beta*r-q.beta*q.x-r^3)*c +
  r^5-r^4*q.x+2*r^4+r^3*q.x-r^3+q.beta*r^4-q.beta*r^3+
    q.beta*r^2*q.x-3*q.beta*r^2+q.beta*r*q.x-q.beta*r-
    q.beta^2*r^2-2*q.beta^2*r+q.beta^2

/-- The positive-root factorization includes all equal-root and beta=0 cases. -/
theorem H_eq_Kmu (q : Tuning) {r : ℝ}
    (hroot : r^2-(1+q.beta-q.x)*r+q.beta=0) (c : ℝ) :
    q.H r c=(1-c)*Kmu q r c := by
  have hid : q.H r c-(1-c)*Kmu q r c =
      (r^2-(1+q.beta-q.x)*r+q.beta) *
      (-2*q.beta*c^2*r+q.beta*c*r^2+q.beta*c-c*r^2*q.y+2*c*r^2-r^3+r*q.y-r) := by
    dsimp [Tuning.H,Kmu]
    ring
  rw [hroot,zero_mul] at hid
  exact sub_eq_zero.mp hid

/-- The negative-root factorization is independent of the sign of other roots. -/
theorem H_eq_KL (q : Tuning) {r : ℝ}
    (hroot : r^2+(1+q.beta-q.y)*r+q.beta=0) (c : ℝ) :
    q.H r c=(1+c)*KL q r c := by
  have hid : q.H r c-(1+c)*KL q r c =
      (r^2+(1+q.beta-q.y)*r+q.beta) *
      (-q.beta*c*r^2-q.beta*c+2*q.beta*r+2*c^2*r^3+c*r^2*q.x-2*c*r^2-r^3-r*q.x+r) := by
    dsimp [Tuning.H,KL]
    ring
  rw [hroot,zero_mul] at hid
  exact sub_eq_zero.mp hid

/-- Exact endpoint formula for the positive-root quotient. -/
theorem Kmu_neg_one (q : Tuning) (r : ℝ) :
    Kmu q r (-1)=(q.beta+r^2)*(1+r)*
      (r^2+(1+q.beta-q.y)*r+q.beta) := by
  dsimp [Kmu]; ring

/-- Exact endpoint formula for the negative-root quotient. -/
theorem KL_one (q : Tuning) (r : ℝ) :
    KL q r 1=(q.beta+r^2)*(1-r)*
      (r^2-(1+q.beta-q.x)*r+q.beta) := by
  dsimp [KL]; ring

/-- Continuity fills the two endpoints after canceling a factor on the interior. -/
theorem nonneg_on_closed_of_open {f : ℝ→ℝ} (hf : Continuous f)
    (h : ∀ c∈Set.Ioo (-1:ℝ) 1,0≤f c) :
    ∀ c∈Set.Icc (-1:ℝ) 1,0≤f c := by
  have hc : IsClosed {c : ℝ | 0≤f c} := isClosed_le continuous_const hf
  have hs : closure (Set.Ioo (-1:ℝ) 1) ⊆ {c : ℝ | 0≤f c} :=
    hc.closure_subset_iff.mpr h
  rw [closure_Ioo (by norm_num : (-1:ℝ)≠1)] at hs
  exact hs

/-- Canceling 1-c preserves the full closed-interval nonnegativity test. -/
theorem H_nonneg_iff_Kmu (q : Tuning) {r : ℝ}
    (hroot : r^2-(1+q.beta-q.x)*r+q.beta=0) :
    (∀ c∈Set.Icc (-1:ℝ) 1,0≤q.H r c) ↔
    (∀ c∈Set.Icc (-1:ℝ) 1,0≤Kmu q r c) := by
  constructor
  · intro h
    apply nonneg_on_closed_of_open (by unfold Kmu; fun_prop)
    intro c hc
    have hh := h c ⟨hc.1.le,hc.2.le⟩
    rw [H_eq_Kmu q hroot] at hh
    exact nonneg_of_mul_nonneg_right hh (by linarith [hc.1,hc.2])
  · intro h c hc
    rw [H_eq_Kmu q hroot]
    exact mul_nonneg (by linarith [hc.2]) (h c hc)

/-- Canceling 1+c likewise retains both endpoints, including c=-1. -/
theorem H_nonneg_iff_KL (q : Tuning) {r : ℝ}
    (hroot : r^2+(1+q.beta-q.y)*r+q.beta=0) :
    (∀ c∈Set.Icc (-1:ℝ) 1,0≤q.H r c) ↔
    (∀ c∈Set.Icc (-1:ℝ) 1,0≤KL q r c) := by
  constructor
  · intro h
    apply nonneg_on_closed_of_open (by unfold KL; fun_prop)
    intro c hc
    have hh := h c ⟨hc.1.le,hc.2.le⟩
    rw [H_eq_KL q hroot] at hh
    exact nonneg_of_mul_nonneg_right hh (by linarith [hc.1,hc.2])
  · intro h c hc
    rw [H_eq_KL q hroot]
    exact mul_nonneg (by linarith [hc.1]) (h c hc)

/-- Exact lower-curvature quotient test, valid with beta=0 as well. -/
theorem Kmu_nonneg_iff (q : Tuning) {r : ℝ} (hr : 0<r) :
    (∀ c∈Set.Icc (-1:ℝ) 1,0≤Kmu q r c) ↔
      0≤Kmu q r (-1) ∧ 0≤Kmu q r 1 ∧
      (q.beta=0 ∨
        (2*r*(r^3*(q.y-1)-q.beta*r^3+q.beta*r^2-2*q.beta*r-q.beta^2))≤ -2*(4*q.beta*r^3) ∨
        2*(4*q.beta*r^3)≤(2*r*(r^3*(q.y-1)-q.beta*r^3+q.beta*r^2-2*q.beta*r-q.beta^2)) ∨
        (2*r*(r^3*(q.y-1)-q.beta*r^3+q.beta*r^2-2*q.beta*r-q.beta^2))^2-
          4*(4*q.beta*r^3)*(Kmu q r 0)≤0) := by
  by_cases hb : q.beta=0
  · simp only [hb,true_or,and_true]
    have he : Kmu q r = quadratic 0 (2*r*(r^3*(q.y-1)))
        (r^5+r^4*q.y-r^3*q.y+r^3) := by
      funext c
      dsimp [Kmu,quadratic]
      rw [hb]
      ring
    rw [he]
    exact concave_quadratic_nonneg_iff (by norm_num)
  · have hb0 : 0<q.beta := lt_of_le_of_ne q.beta_nonneg (Ne.symm hb)
    have he : Kmu q r = quadratic (4*q.beta*r^3)
        (2*r*(r^3*(q.y-1)-q.beta*r^3+q.beta*r^2-2*q.beta*r-q.beta^2)) (Kmu q r 0) := by
      funext c; dsimp [Kmu,quadratic]; ring
    have hh := convex_quadratic_nonneg_iff (b :=
      2*r*(r^3*(q.y-1)-q.beta*r^3+q.beta*r^2-2*q.beta*r-q.beta^2))
      (d := Kmu q r 0) (by positivity : 0<4*q.beta*r^3)
    simp only [hb,false_or]
    simpa only [← he] using hh

/-- The upper-curvature quotient is concave, so endpoints suffice. -/
theorem KL_nonneg_iff (q : Tuning) {r : ℝ} (hr : 0≤r) :
    (∀ c∈Set.Icc (-1:ℝ) 1,0≤KL q r c) ↔ 0≤KL q r (-1) ∧ 0≤KL q r 1 := by
  have he : KL q r=quadratic (-4*q.beta*r^3)
      (2*r^2*(q.beta^2+3*q.beta+q.beta*r-q.beta*q.x-r^3)) (KL q r 0) := by
    funext c; dsimp [KL,quadratic]; ring
  rw [he]
  exact concave_quadratic_nonneg_iff (by nlinarith [mul_nonneg q.beta_nonneg (pow_nonneg hr 3)])

end
end polyak.General.Regions
