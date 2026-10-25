import polyak.Numerics.Taylor
import polyak.Numerics.Modular

/-!
Article: Appendix B, exact rational P₂ identities.
Use: a compact coefficient pair certifies a specified real source function.
Every cancellation is an exact polynomial identity with a separate proof that
the new denominator is nonzero on the actual parameter set.
-/

namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial

/-- Article: executable equality of two independently supplied rational coefficient arrays. -/
def polynomialCheck (p q : QPoly) : Bool := decide (p.trim=q.trim)

/-- Article: finite coefficient equality implies semantic polynomial equality. -/
theorem polynomialCheck_sound {p q : QPoly} (h : polynomialCheck p q=true) : p.toPoly=q.toPoly := by
  have he : p.trim=q.trim := of_decide_eq_true h
  simpa only [QPoly.toPoly_trim] using congrArg QPoly.toPoly he

/-- Article: source-linked exact rational representation throughout a parameter set. -/
structure RationalCode (S : Set ℝ) (source : ℝ → ℝ) where
  /-- Article: exact numerator coefficient proposal. -/
  numerator : QPoly
  /-- Article: exact denominator coefficient proposal. -/
  denominator : QPoly
  /-- Article: divisions are justified at every parameter under consideration. -/
  denominator_ne : ∀ z∈S, aeval z denominator.toPoly≠0
  /-- Article: the checked representation denotes the original real source formula. -/
  exact : ∀ z∈S, source z=aeval z numerator.toPoly/aeval z denominator.toPoly

variable {S : Set ℝ} {f g : ℝ → ℝ}

/-- Article: a constant has denominator one. -/
def RationalCode.constant (S : Set ℝ) (a : ℚ) : RationalCode S (fun _ => (a : ℝ)) where
  numerator := QPoly.constant a
  denominator := QPoly.constant 1
  denominator_ne _ _ := by simp [QPoly.toPoly_constant]
  exact _ _ := by simp [QPoly.toPoly_constant]

/-- Article: the true parameter variable has denominator one. -/
def RationalCode.variable (S : Set ℝ) : RationalCode S id where
  numerator := QPoly.X
  denominator := QPoly.constant 1
  denominator_ne _ _ := by simp [QPoly.toPoly_constant]
  exact _ _ := by simp [QPoly.toPoly_constant,QPoly.toPoly_X]

/-- Article: source-preserving recoding, with an exact checked cross product. -/
def RationalCode.recode (F : RationalCode S f) (p q : QPoly)
    (hq : ∀ z∈S, aeval z q.toPoly≠0)
    (hc : polynomialCheck (F.numerator.mul q) (p.mul F.denominator)=true) : RationalCode S f where
  numerator := p
  denominator := q
  denominator_ne := hq
  exact z hz := by
    rw [F.exact z hz]
    apply (div_eq_div_iff (F.denominator_ne z hz) (hq z hz)).mpr
    have he := congrArg (aeval z) (polynomialCheck_sound hc)
    simpa only [QPoly.toPoly_mul,map_mul] using he

/-- Article: exact addition before optional cancellation of polynomial factors. -/
def RationalCode.add (F : RationalCode S f) (G : RationalCode S g) :
    RationalCode S (fun z => f z+g z) where
  numerator := (F.numerator.mul G.denominator).add (G.numerator.mul F.denominator)
  denominator := F.denominator.mul G.denominator
  denominator_ne z hz := by
    rw [QPoly.toPoly_mul,map_mul]
    exact mul_ne_zero (F.denominator_ne z hz) (G.denominator_ne z hz)
  exact z hz := by
    rw [F.exact z hz,G.exact z hz,QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_mul,
      QPoly.toPoly_mul,map_add,map_mul,map_mul,map_mul]
    simpa only [mul_comm] using div_add_div _ _ (F.denominator_ne z hz) (G.denominator_ne z hz)

/-- Article: exact multiplication before optional cancellation. -/
def RationalCode.mul (F : RationalCode S f) (G : RationalCode S g) :
    RationalCode S (fun z => f z*g z) where
  numerator := F.numerator.mul G.numerator
  denominator := F.denominator.mul G.denominator
  denominator_ne z hz := by
    rw [QPoly.toPoly_mul,map_mul]
    exact mul_ne_zero (F.denominator_ne z hz) (G.denominator_ne z hz)
  exact z hz := by
    rw [F.exact z hz,G.exact z hz,QPoly.toPoly_mul,QPoly.toPoly_mul,map_mul,map_mul,mul_div_mul_comm]

/-- Article: reciprocal requires a proved nonzero source numerator. -/
def RationalCode.inv (F : RationalCode S f)
    (hp : ∀ z∈S, aeval z F.numerator.toPoly≠0) : RationalCode S (fun z => (f z)⁻¹) where
  numerator := F.denominator
  denominator := F.numerator
  denominator_ne := hp
  exact z hz := by rw [F.exact z hz,inv_div]

/-- Article: executable polynomial powering contains no semantic proof transports. -/
def polynomialPower (p : QPoly) : ℕ → QPoly
  | 0 => QPoly.constant 1
  | n+1 => (polynomialPower p n).mul p

/-- Article: coefficient powering denotes the actual polynomial power. -/
theorem polynomialPower_sound (p : QPoly) (n : ℕ) :
    (polynomialPower p n).toPoly=p.toPoly^n := by
  induction n with
  | zero => simp [polynomialPower,QPoly.toPoly_constant]
  | succ n ih => rw [polynomialPower,QPoly.toPoly_mul,ih,pow_succ]

/-- Article: powers preserve the actual source formula and nonzero denominator. -/
def RationalCode.pow (F : RationalCode S f) (n : ℕ) : RationalCode S (fun z => f z^n) where
  numerator := polynomialPower F.numerator n
  denominator := polynomialPower F.denominator n
  denominator_ne z hz := by
    rw [polynomialPower_sound,map_pow]
    exact pow_ne_zero n (F.denominator_ne z hz)
  exact z hz := by
    rw [F.exact z hz,polynomialPower_sound,polynomialPower_sound,map_pow,map_pow,div_pow]

/-- Article: nonzero numerator and denominator prove the specified source is nonzero. -/
theorem RationalCode.ne_zero (F : RationalCode S f)
    (hp : ∀ z∈S, aeval z F.numerator.toPoly≠0) {z : ℝ} (hz : z∈S) : f z≠0 := by
  rw [F.exact z hz]
  exact div_ne_zero (hp z hz) (F.denominator_ne z hz)

/-- Article: a checked zero numerator proves the actual rational source identity. -/
theorem RationalCode.eq_zero (F : RationalCode S f)
    (hc : polynomialCheck F.numerator QPoly.zero=true) {z : ℝ} (hz : z∈S) : f z=0 := by
  rw [F.exact z hz,polynomialCheck_sound hc]
  simp only [QPoly.toPoly_zero,map_zero,zero_div]

end
end polyak.Boundary.P2
