import polyak.Numerics.BivariateBranch

/-!
Article: exact rational identities for the initialized spiral.
Use: executable bivariate coefficient arithmetic certifies independently
specified real formulas, with every denominator proved nonzero.
Proof: structural Horner identities and exact rational coefficient equality.
-/

namespace polyak.Numerics.BivariateBranch
open LeanCert.Engine

/-- Article: the empty coefficient array evaluates to zero. -/
@[simp] theorem value_nil (r x : ℝ) : value [] r x=0 := rfl

/-- Article: Horner's source evaluation at the next q coefficient. -/
@[simp] theorem value_cons (p : QPoly) (ps : Code) (r x : ℝ) :
    value (p::ps) r x=Polynomial.aeval r p.toPoly+x*value ps r x := rfl

/-- Article: coefficientwise polynomial addition, retaining explicit zero coefficients. -/
def add : Code → Code → Code
  | [],q => q
  | p,[] => p
  | p::ps,q::qs => p.add q::add ps qs

/-- Article: multiply every q coefficient by a polynomial in ρ. -/
def scale (a : QPoly) (p : Code) : Code := p.map a.mul

/-- Article: multiplication by the convolution recurrence. -/
def mul : Code → Code → Code
  | [],_ => []
  | p::ps,q => add (scale p q) (QPoly.zero::mul ps q)

/-- Article: exact Horner evaluation respects coefficientwise addition. -/
theorem value_add (p q : Code) (r x : ℝ) : value (add p q) r x=value p r x+value q r x := by
  induction p generalizing q with
  | nil => simp [add,value]
  | cons p ps ih =>
    cases q with
    | nil => simp [add,value]
    | cons q qs =>
      simp only [add,value_cons,QPoly.toPoly_add,map_add,ih]
      ring

/-- Article: scaling a coefficient array multiplies its actual polynomial. -/
theorem value_scale (a : QPoly) (p : Code) (r x : ℝ) :
    value (scale a p) r x=Polynomial.aeval r a.toPoly*value p r x := by
  induction p with
  | nil => simp [scale,value]
  | cons p ps ih =>
    simp only [scale,List.map_cons,value_cons,QPoly.toPoly_mul,map_mul] at *
    rw [ih]
    ring

/-- Article: convolution computes the actual product, with no appeal to native arithmetic. -/
theorem value_mul (p q : Code) (r x : ℝ) : value (mul p q) r x=value p r x*value q r x := by
  induction p with
  | nil => simp [mul,value]
  | cons p ps ih =>
    rw [mul,value_add,value_scale]
    simp only [value_cons,QPoly.toPoly_zero,map_zero,zero_add] at *
    rw [ih]
    ring

/-- Article: exact powers on executable bivariate arrays, with no dependent type transport. -/
def power (p : Code) : ℕ → Code
  | 0 => [QPoly.constant 1]
  | n+1 => mul (power p n) p

/-- Article: executable powers denote the source polynomial powers. -/
theorem value_power (p : Code) (n : ℕ) (r x : ℝ) : value (power p n) r x=value p r x^n := by
  induction n with
  | zero => simp [power,QPoly.toPoly_constant]
  | succ n ih => rw [power,value_mul,ih,pow_succ]

/-- Article: remove zero q coefficients from the high-degree end. -/
def trim : Code → Code
  | [] => []
  | p::ps =>
    match trim ps with
    | [] => if p.trim.coeffs.isEmpty then [] else [p.trim]
    | q::qs => p.trim::q::qs

/-- Article: trimming retains the same actual real polynomial. -/
theorem value_trim (p : Code) (r x : ℝ) : value (trim p) r x=value p r x := by
  induction p with
  | nil => rfl
  | cons p ps ih =>
    simp only [trim]
    split
    · next ht =>
      have hz : value ps r x=0 := by rw [← ih,ht]; rfl
      split
      · next hp =>
        have hempty : p.trim.coeffs=#[] := Array.isEmpty_iff.mp hp
        have he : p.trim=QPoly.zero := congrArg QPoly.mk hempty
        have hpoly : p.toPoly=0 := by rw [← QPoly.toPoly_trim,he,QPoly.toPoly_zero]
        simp only [value_nil,value_cons,hpoly,map_zero,hz,mul_zero,add_zero]
      · simp only [value_cons,value_nil,QPoly.toPoly_trim,hz,mul_zero,add_zero]
    · next q qs ht =>
      have hh : value (q::qs) r x=value ps r x := by rw [← ht]; exact ih
      simp only [value_cons,QPoly.toPoly_trim] at *
      rw [hh]

/-- Article: executable exact equality of bivariate polynomials. -/
def equalCheck (p q : Code) : Bool := decide (trim p=trim q)

/-- Article: coefficient equality proves equality of the source evaluations. -/
theorem equalCheck_sound {p q : Code} (h : equalCheck p q=true) (r x : ℝ) :
    value p r x=value q r x := by
  have he : trim p=trim q := of_decide_eq_true h
  rw [← value_trim p,he,value_trim]

/-- Article: a source-linked rational identity on its actual domain. -/
structure RationalCode (S : Set (ℝ×ℝ)) (f : ℝ×ℝ → ℝ) where
  /-- Article: exact numerator proposal. -/
  numerator : Code
  /-- Article: exact denominator proposal. -/
  denominator : Code
  /-- Article: zero denominators are excluded mathematically on the actual domain. -/
  denominator_ne : ∀ z∈S,value denominator z.1 z.2≠0
  /-- Article: the independently specified source equals its checked representation. -/
  exact : ∀ z∈S,f z=value numerator z.1 z.2/value denominator z.1 z.2

noncomputable section
variable {S : Set (ℝ×ℝ)} {f g : ℝ×ℝ → ℝ}

/-- Article: a proved pointwise identity changes the source name, never the checked data. -/
def RationalCode.congr (F : RationalCode S f) (he : ∀ z∈S,f z=g z) : RationalCode S g where
  numerator := F.numerator
  denominator := F.denominator
  denominator_ne := F.denominator_ne
  exact z hz := (he z hz).symm.trans (F.exact z hz)

/-- Article: exact rational constants have denominator one. -/
def RationalCode.constant (S : Set (ℝ×ℝ)) (a : ℚ) : RationalCode S (fun _ => (a : ℝ)) where
  numerator := [QPoly.constant a]
  denominator := [QPoly.constant 1]
  denominator_ne _ _ := by simp [QPoly.toPoly_constant]
  exact _ _ := by simp [QPoly.toPoly_constant]

/-- Article: the actual growth-factor parameter is the first coordinate. -/
def RationalCode.first (S : Set (ℝ×ℝ)) : RationalCode S Prod.fst where
  numerator := [QPoly.X]
  denominator := [QPoly.constant 1]
  denominator_ne _ _ := by simp [QPoly.toPoly_constant]
  exact _ _ := by simp [QPoly.toPoly_X,QPoly.toPoly_constant]

/-- Article: the physical condition parameter is the second coordinate. -/
def RationalCode.second (S : Set (ℝ×ℝ)) : RationalCode S Prod.snd where
  numerator := [QPoly.zero,QPoly.constant 1]
  denominator := [QPoly.constant 1]
  denominator_ne _ _ := by simp [QPoly.toPoly_constant]
  exact _ _ := by simp [QPoly.toPoly_zero,QPoly.toPoly_constant]

/-- Article: source-preserving recoding requires an exact checked cross-product. -/
def RationalCode.recode (F : RationalCode S f) (p q : Code)
    (hq : ∀ z∈S,value q z.1 z.2≠0)
    (hc : equalCheck (mul F.numerator q) (mul p F.denominator)=true) : RationalCode S f where
  numerator := p
  denominator := q
  denominator_ne := hq
  exact z hz := by
    rw [F.exact z hz]
    apply (div_eq_div_iff (F.denominator_ne z hz) (hq z hz)).mpr
    simpa only [value_mul] using equalCheck_sound hc z.1 z.2

/-- Article: addition preserves source semantics before exact cancellation. -/
def RationalCode.add (F : RationalCode S f) (G : RationalCode S g) :
    RationalCode S (fun z => f z+g z) where
  numerator := BivariateBranch.add (BivariateBranch.mul F.numerator G.denominator)
    (BivariateBranch.mul G.numerator F.denominator)
  denominator := BivariateBranch.mul F.denominator G.denominator
  denominator_ne z hz := by rw [value_mul]; exact mul_ne_zero (F.denominator_ne z hz) (G.denominator_ne z hz)
  exact z hz := by
    rw [F.exact z hz,G.exact z hz,value_add,value_mul,value_mul,value_mul]
    simpa only [mul_comm] using div_add_div _ _ (F.denominator_ne z hz) (G.denominator_ne z hz)

/-- Article: multiplication preserves source semantics. -/
def RationalCode.mul (F : RationalCode S f) (G : RationalCode S g) :
    RationalCode S (fun z => f z*g z) where
  numerator := BivariateBranch.mul F.numerator G.numerator
  denominator := BivariateBranch.mul F.denominator G.denominator
  denominator_ne z hz := by rw [value_mul]; exact mul_ne_zero (F.denominator_ne z hz) (G.denominator_ne z hz)
  exact z hz := by rw [F.exact z hz,G.exact z hz,value_mul,value_mul,mul_div_mul_comm]

/-- Article: reciprocal requires a nonzero source numerator. -/
def RationalCode.inv (F : RationalCode S f) (hp : ∀ z∈S,value F.numerator z.1 z.2≠0) :
    RationalCode S (fun z => (f z)⁻¹) where
  numerator := F.denominator
  denominator := F.numerator
  denominator_ne := hp
  exact z hz := by rw [F.exact z hz,inv_div]

/-- Article: a nonzero actual source suffices for a justified reciprocal. -/
def RationalCode.invOfSource (F : RationalCode S f) (hf : ∀ z∈S,f z≠0) :
    RationalCode S (fun z => (f z)⁻¹) := F.inv (by
  intro z hz hn
  have hh := hf z hz
  rw [F.exact z hz,hn,zero_div] at hh
  exact hh rfl)

/-- Article: exact powers preserve the independent source formula. -/
def RationalCode.pow (F : RationalCode S f) (n : ℕ) : RationalCode S (fun z => f z^n) where
  numerator := power F.numerator n
  denominator := power F.denominator n
  denominator_ne z hz := by rw [value_power]; exact pow_ne_zero _ (F.denominator_ne z hz)
  exact z hz := by rw [value_power,value_power,F.exact z hz,div_pow]

/-- Article: exact negation preserves the independent source formula. -/
def RationalCode.neg (F : RationalCode S f) : RationalCode S (fun z => -(f z)) := by
  simpa only [Rat.cast_neg,Rat.cast_one,neg_one_mul] using (RationalCode.constant S (-1)).mul F

/-- Article: subtraction preserves the independent source formula. -/
def RationalCode.sub (F : RationalCode S f) (G : RationalCode S g) :
    RationalCode S (fun z => f z-g z) := by
  simpa only [sub_eq_add_neg] using F.add G.neg

/-- Article: exact division requires a nonzero actual denominator source. -/
def RationalCode.div (F : RationalCode S f) (G : RationalCode S g)
    (hg : ∀ z∈S,g z≠0) : RationalCode S (fun z => f z/g z) := by
  simpa only [div_eq_mul_inv] using F.mul (G.invOfSource hg)

end
end polyak.Numerics.BivariateBranch
