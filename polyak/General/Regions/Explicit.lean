import polyak.General.Cubic
import polyak.General.Regions.Quadratics

/-! Article: Corollary C(a,b), exact explicit lag-one region.
The frequency continuum is retained; beta=0 and zero discriminants are separate.
-/
namespace polyak.General.Regions
noncomputable section

/-- The lag-one region in the source cosine coordinate. -/
def OmegaOne (q : Tuning) : Prop := ∀ c∈Set.Icc (-1:ℝ) 1, 0<q.L c

/-- Coefficient of the linear term of the lag-one quadratic. -/
def linearCoefficient (q : Tuning) : ℝ :=
  2*(q.y-1-2*q.beta-q.beta^2+q.beta*q.x)

/-- Constant term of the lag-one quadratic. -/
def constantCoefficient (q : Tuning) : ℝ :=
  2-2*q.x+q.x*q.y+2*q.beta^2-2*q.beta*q.y

/-- The vertex formula in Corollary C. -/
def vertex (q : Tuning) : ℝ :=
  (1+2*q.beta+q.beta^2-q.beta*q.x-q.y)/(4*q.beta)

/-- The discriminant with the harmless positive factor four removed. -/
def discriminant (q : Tuning) : ℝ :=
  (q.y-1-2*q.beta-q.beta^2+q.beta*q.x)^2-
    4*q.beta*(2-2*q.x+q.x*q.y+2*q.beta^2-2*q.beta*q.y)

theorem L_eq_quadratic (q : Tuning) (c : ℝ) :
    q.L c=quadratic (4*q.beta) (linearCoefficient q) (constantCoefficient q) c := rfl

theorem vertex_outside_iff (q : Tuning) (hb : 0<q.beta) :
    vertex q∉Set.Ioo (-1:ℝ) 1 ↔
      linearCoefficient q≤ -2*(4*q.beta) ∨ 2*(4*q.beta)≤linearCoefficient q := by
  have h1 : -1<vertex q ↔ linearCoefficient q<2*(4*q.beta) := by
    dsimp [vertex,linearCoefficient]
    rw [lt_div_iff₀ (by positivity : 0<4*q.beta)]
    constructor <;> intro h <;> linarith
  have h2 : vertex q<1 ↔ -2*(4*q.beta)<linearCoefficient q := by
    dsimp [vertex,linearCoefficient]
    rw [div_lt_iff₀ (by positivity : 0<4*q.beta)]
    constructor <;> intro h <;> linarith
  simp only [Set.mem_Ioo,h1,h2,not_and_or,not_lt]
  tauto

/-- Corollary C(a), literal vertex/discriminant formula, including beta=0. -/
theorem omegaOne_iff_explicit (q : Tuning) :
    OmegaOne q ↔ q.beta=0 ∨ vertex q∉Set.Ioo (-1:ℝ) 1 ∨ discriminant q<0 := by
  by_cases hb : q.beta=0
  · simp only [hb,true_or,iff_true]
    intro c hc
    rw [L_eq_quadratic q]
    simp only [hb,mul_zero]
    apply linear_quadratic_pos
    · simpa only [L_eq_quadratic q,hb,mul_zero] using q.L_neg_one_pos
    · simpa only [L_eq_quadratic q,hb,mul_zero] using q.L_one_pos
    · exact hc
  · have hb0 : 0<q.beta := lt_of_le_of_ne q.beta_nonneg (Ne.symm hb)
    have hd : linearCoefficient q^2-4*(4*q.beta)*constantCoefficient q=
        4*discriminant q := by
      dsimp [linearCoefficient,constantCoefficient,discriminant]; ring
    change (∀ c∈Set.Icc (-1:ℝ) 1,0<q.L c) ↔ _
    simp only [L_eq_quadratic q]
    rw [convex_quadratic_pos_iff (by positivity : 0<4*q.beta)]
    have hl : 0<quadratic (4*q.beta) (linearCoefficient q) (constantCoefficient q) (-1) :=
      q.L_neg_one_pos
    have hr : 0<quadratic (4*q.beta) (linearCoefficient q) (constantCoefficient q) 1 :=
      q.L_one_pos
    simp only [hl,hr,true_and,hb,false_or]
    rw [vertex_outside_iff q hb0,hd]
    constructor
    · rintro (h|h|h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (by linarith)
    · rintro (h|h)
      · rcases h with h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by linarith))

/-- The exact algebraic angle threshold in Corollary C(b), with arbitrary h. -/
theorem Xi_ge_iff_L_le (q : Tuning) (c h : ℝ) :
    h≤q.Xi c ↔ q.L c≤(q.y-q.x)*(1-q.beta)*(1+c-h) := by
  rw [q.L_eq_Xi]
  have hp : 0<(q.y-q.x)*(1-q.beta) := mul_pos (sub_pos.mpr q.x_lt_y)
    (sub_pos.mpr q.beta_lt_one)
  constructor <;> intro hh
  · exact mul_le_mul_of_nonneg_left (by linarith) hp.le
  · have := (mul_le_mul_iff_right₀ hp).mp hh
    linarith

/-- For the j=1 angle threshold, h=1+c and the right-hand side vanishes. -/
theorem Xi_ge_one_add_iff_L_nonpos (q : Tuning) (c : ℝ) :
    1+c≤q.Xi c ↔ q.L c≤0 := by
  simpa only [sub_self,mul_zero] using Xi_ge_iff_L_le q c (1+c)

end
end polyak.General.Regions
