import polyak.Waves.Polyak

/-!
Article: (spiralsimple), Lemma spiralids, and Proposition spiral.
Use: exact one-atom spiral data and all lag identities. The argument uses
division-free Chebyshev identities and therefore retains both frequency endpoints.
-/

noncomputable section

namespace polyak.Spiral

open Spectral

/-- Article: G=cosh t. -/
def G (t : ℝ) : ℝ := Real.cosh t

/-- Article: the spiral twist u. -/
def twist (t : ℝ) : ℝ := 1-1/(2*G t)

/-- Article: the spiral cosine frequency c. -/
def cosine (t : ℝ) : ℝ := -1/(2*G t)

/-- Article: the exact positive minimizer slack g. -/
def gap (t : ℝ) : ℝ := (2*G t-1)/(2*G t^2)

/-- Article: the common function-value constant C=g tanh t. -/
def valueConstant (t : ℝ) : ℝ := gap t*Real.sinh t/G t

/-- Article: E_n(t), in polynomial cosine coordinates. -/
def kernel (t : ℝ) (n : ℕ) : ℝ :=
  Real.cosh (n*t)+2*G t^2*chebT n (cosine t)

/-- Article: G≥1, including t=0. -/
theorem one_le_G (t : ℝ) : 1 ≤ G t := Real.one_le_cosh t

/-- Article: G is a positive denominator everywhere. -/
theorem G_pos (t : ℝ) : 0 < G t := zero_lt_one.trans_le (one_le_G t)

/-- Article: the one atom belongs to the exact frequency interval. -/
theorem cosine_mem (t : ℝ) : cosine t ∈ Set.Icc (-1 : ℝ) 1 := by
  have hg := G_pos t
  have hG := one_le_G t
  unfold cosine
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2*G t)).mpr
    linarith
  · exact (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)).trans (by norm_num)

/-- Article: the actual atom, with frequency endpoints retained by the carrier. -/
def atom (t : ℝ) : Frequency := ⟨cosine t, cosine_mem t⟩

/-- Article: the Dirac spectrum of the special spiral. -/
def spectrum (t : ℝ) : Spectrum := ⟨MeasureTheory.Measure.dirac (atom t), by infer_instance⟩

/-- Article: averaging on the one-atom spiral is exact evaluation. -/
theorem avg_spectrum (t : ℝ) (f : Frequency → ℝ) : avg (spectrum t) f = f (atom t) := by
  simp [avg, spectrum]

/-- Article: g=(2G−1)/(2G²). Proof: substitution into the original g. -/
theorem g_spiral (t : ℝ) : Spectral.g (twist t) (cosine t) = gap t := by
  have hg := (G_pos t).ne'
  unfold Spectral.g twist cosine gap
  field_simp
  ring

/-- Article: a useful exact relation between the twist and minimizer slack. -/
theorem twist_eq_G_mul_gap (t : ℝ) : twist t = G t*gap t := by
  have hg := (G_pos t).ne'
  unfold twist gap
  field_simp

/-- Article: g is strictly positive, also on the limiting three-cycle. -/
theorem gap_pos (t : ℝ) : 0 < gap t := by
  have hg := G_pos t
  have hG := one_le_G t
  unfold gap
  apply div_pos (by linarith)
  positivity

/-- Article: cosine shift identity in the exact Chebyshev normalization. -/
theorem chebT_shift_up (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (1-c^2)*chebU (n-1) c = c*chebT n c-chebT (n+1) c := by
  have h := congrArg (Polynomial.eval c)
    (Polynomial.Chebyshev.T_eq_X_mul_T_sub_pol_U ℝ ((n : ℤ)-1))
  have hm : ((n-1 : ℕ) : ℤ) = (n : ℤ)-1 := by omega
  have h₁ : (n : ℤ)-1+1 = n := by omega
  have h₂ : (n : ℤ)-1+2 = ((n+1 : ℕ) : ℤ) := by omega
  simp only [h₁, h₂, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_pow] at h
  change (1-c^2)*(Polynomial.Chebyshev.U ℝ ((n-1 : ℕ) : ℤ)).eval c =
    c*(Polynomial.Chebyshev.T ℝ (n : ℤ)).eval c-
      (Polynomial.Chebyshev.T ℝ ((n+1 : ℕ) : ℤ)).eval c
  rw [hm]
  linarith

/-- Article: the reversed cosine shift identity. -/
theorem chebT_shift_down (c : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    chebT (n-1) c = 2*c*chebT n c-chebT (n+1) c := by
  have h := congrArg (Polynomial.eval c) (Polynomial.Chebyshev.T_sub_one ℝ (n : ℤ))
  have hm : ((n-1 : ℕ) : ℤ) = (n : ℤ)-1 := by omega
  simpa only [chebT, hm, Nat.cast_add, Nat.cast_one, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X] using h

/-- Article: lower hyperbolic shift, without division by sinh t. -/
theorem cosh_shift_up (t : ℝ) (n : ℕ) :
    Real.cosh ((n+1 : ℕ)*t) = G t*Real.cosh (n*t)+Real.sinh t*Real.sinh (n*t) := by
  rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Real.cosh_add]
  unfold G
  ring

/-- Article: upper hyperbolic shift, also valid when sinh t=0. -/
theorem cosh_shift_down (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Real.cosh ((n-1 : ℕ)*t) = G t*Real.cosh (n*t)-Real.sinh t*Real.sinh (n*t) := by
  have hm : ((n-1 : ℕ) : ℝ)*t = n*t-t := by
    rw [Nat.cast_sub hn, Nat.cast_one]
    ring
  rw [hm, Real.cosh_sub]
  unfold G
  ring

/-- Article: all lower lag identities in (En), in the original raw slack normalization. -/
theorem lag_lower_eq (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    lagA (twist t) t n (cosine t)-lagB (twist t) n (cosine t)+
      valueConstant t*Real.sinh (n*t) = gap t/G t*kernel t (n+1) := by
  have hg := (G_pos t).ne'
  have hT := chebT_shift_up (cosine t) n hn
  rw [lagA, lagD, g_spiral, lagB, twist_eq_G_mul_gap]
  unfold valueConstant kernel
  rw [cosh_shift_up]
  have hc : 2*G t*cosine t = -1 := by unfold cosine; field_simp
  field_simp
  linear_combination -2*(G t)^2*(gap t)*hT - G t*gap t*chebT n (cosine t)*hc

/-- Article: all upper lag identities in (En), in the original raw slack normalization. -/
theorem lag_upper_eq (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    lagA (twist t) t n (cosine t)+lagB (twist t) n (cosine t)-
      valueConstant t*Real.sinh (n*t) = gap t/G t*kernel t (n-1) := by
  have hg := (G_pos t).ne'
  have hT := chebT_shift_up (cosine t) n hn
  have hD := chebT_shift_down (cosine t) n hn
  rw [lagA, lagD, g_spiral, lagB, twist_eq_G_mul_gap]
  unfold valueConstant kernel
  rw [cosh_shift_down t n hn]
  have hc : 2*G t*cosine t = -1 := by unfold cosine; field_simp
  field_simp
  linear_combination 2*(G t)^2*gap t*hT -
    2*(G t)^2*gap t*hD -G t*gap t*chebT n (cosine t)*hc

/-- Article: E₀=1+2G². -/
@[simp] theorem kernel_zero (t : ℝ) : kernel t 0 = 1+2*G t^2 := by simp [kernel, chebT]

/-- Article: E₁=0. -/
@[simp] theorem kernel_one (t : ℝ) : kernel t 1 = 0 := by
  have hg := (G_pos t).ne'
  simp only [kernel, Nat.cast_one, one_mul, chebT, Polynomial.Chebyshev.T_one,
    Polynomial.eval_X]
  change G t+2*G t^2*cosine t = 0
  unfold cosine
  field_simp
  ring

/-- Article: E₂=0. -/
@[simp] theorem kernel_two (t : ℝ) : kernel t 2 = 0 := by
  have hg := (G_pos t).ne'
  simp only [kernel, Nat.cast_ofNat, chebT, Polynomial.Chebyshev.T_two,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  rw [Real.cosh_two_mul, Real.sinh_sq]
  change G t^2+(G t^2-1)+2*G t^2*(2*cosine t^2-1) = 0
  unfold cosine
  field_simp
  ring

end polyak.Spiral
