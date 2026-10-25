import polyak.Realization.ExplicitSpiral.Phase

/-!
Article: the finite exact signs for the Y=2 initialized special spiral.
Use: mathematical rational source formulas are specified independently of
all executable coefficient arrays, box annotations, and sign witnesses.
The imaginary-coordinate coefficients factor out Im λ; its square is explicit.
-/

namespace polyak.Realization.ExplicitSpiral.Source
noncomputable section

/-- Article: the physical domain before imposing the master equation. -/
def domain : Set (ℝ×ℝ) := {z | 0<z.1 ∧ 0<z.2}

/-- Article: G=(ρ+ρ⁻¹)/2. -/
def hyperbolic (r : ℝ) : ℝ := (r+1/r)/2

/-- Article: g on the special spiral. -/
def gap (r : ℝ) : ℝ := 2*r*(r^2-r+1)/(r^2+1)^2

/-- Article: Re λ from the exact spiral cosine. -/
def lambdaReal (r : ℝ) : ℝ := -r^2/(r^2+1)

/-- Article: (Im λ)² from |λ|²=ρ² and the exact real part. -/
def imaginarySquare (r : ℝ) : ℝ := r^2-lambdaReal r^2

/-- Article: Re s, with s=(λ+q²/λ)/(2q). -/
def multiplierReal (r q : ℝ) : ℝ := -(r^2+q^2)/(2*q*(r^2+1))

/-- Article: Im s divided by Im λ. -/
def multiplierImag (r q : ℝ) : ℝ := (r^2-q^2)/(2*q*r^2)

/-- Article: Re Δ for Δ=q(1-λ⁻¹)/2. -/
def defectReal (r q : ℝ) : ℝ := q*(r^2+2)/(2*(r^2+1))

/-- Article: Im Δ divided by Im λ. -/
def defectImag (r q : ℝ) : ℝ := q/(2*r^2)

/-- Article: the fixed defect norm, with no trigonometric approximation. -/
def defectNorm (r q : ℝ) : ℝ := defectReal r q^2+imaginarySquare r*defectImag r q^2

/-- Article: Re α, where α=conj(Δ)(s-δ)/2. -/
def alphaReal (r q δ : ℝ) : ℝ :=
  (defectReal r q*(multiplierReal r q-δ)+
    imaginarySquare r*defectImag r q*multiplierImag r q)/2

/-- Article: Im α divided by Im λ. -/
def alphaImag (r q δ : ℝ) : ℝ :=
  (defectReal r q*multiplierImag r q-defectImag r q*(multiplierReal r q-δ))/2

/-- Article: Re βδ, for δ=-1 (lower) or +1 (upper). -/
def betaReal (r q δ : ℝ) : ℝ := gap r*hyperbolic r*lambdaReal r/r+alphaReal r q δ

/-- Article: Im βδ divided by Im λ. -/
def betaImag (r q δ : ℝ) : ℝ := δ*gap r*hyperbolic r/r+alphaImag r q δ

/-- Article: |βδ|², retaining the exact phase information. -/
def betaNorm (r q δ : ℝ) : ℝ := betaReal r q δ^2+imaginarySquare r*betaImag r q δ^2

/-- Article: the nonoscillating coefficient aδ. -/
def quadratic (r δ : ℝ) : ℝ := gap r/(4*hyperbolic r)*((1-δ)/(2*r)+(1+δ)*r/2)

/-- Article: the constant γδ. -/
def constant (r q δ : ℝ) : ℝ :=
  gap r/(4*hyperbolic r)*((1-δ)*r/2+(1+δ)/(2*r))-
    alphaReal r q δ-defectNorm r q/4

/-- Article: A₀=(1-q⁴)², the uniform positive scalar reserve. -/
def reserve (q : ℝ) : ℝ := (1-q^4)^2

/-- Article: Re(βδ exp(i j ω)), with j=0,1,2 in the finite sign list. -/
def residue (r q δ : ℝ) (j : ℕ) : ℝ :=
  if j=0 then betaReal r q δ else
    betaReal r q δ*polyak.Spectral.chebT j (radialCosine r)-
      imaginarySquare r/r*betaImag r q δ*polyak.Spectral.chebU (j-1) (radialCosine r)

/-- Article: the value coefficient b=(C+2 Re s)/4. -/
def valueConstant (r q : ℝ) : ℝ :=
  (gap r*(r^2-1)/(r^2+1)+2*multiplierReal r q)/4

/-- Article: Re λᵏ expressed in the exact cosine polynomial. -/
def powerReal (r : ℝ) (k : ℕ) : ℝ := r^k*polyak.Spectral.chebT k (radialCosine r)

/-- Article: Im λᵏ divided by Im λ. -/
def powerImag (r : ℝ) (k : ℕ) : ℝ :=
  if k=0 then 0 else r^(k-1)*polyak.Spectral.chebU (k-1) (radialCosine r)

/-- Article: Re(sλᵏ). -/
def gradientReal (r q : ℝ) (k : ℕ) : ℝ :=
  multiplierReal r q*powerReal r k-imaginarySquare r*multiplierImag r q*powerImag r k

/-- Article: Im(sλᵏ) divided by Im λ. -/
def gradientImag (r q : ℝ) (k : ℕ) : ℝ :=
  multiplierReal r q*powerImag r k+multiplierImag r q*powerReal r k

/-- Article: the exact corrected planar radius at a fixed positive time. -/
def radius (r q : ℝ) (k : ℕ) : ℝ :=
  ((powerReal r k-1)^2+imaginarySquare r*powerImag r k^2-
    (gradientReal r q k-(multiplierReal r q+defectReal r q))^2-
      imaginarySquare r*(gradientImag r q k-(multiplierImag r q+defectImag r q))^2)/4

/-- Article: the exact corrected discrepancy at a fixed positive time. -/
def discrepancy (r q : ℝ) (k : ℕ) : ℝ :=
  valueConstant r q*(r^(2*k)-1)-
    ((multiplierReal r q+defectReal r q+gradientReal r q k)*(powerReal r k-1)+
      imaginarySquare r*(multiplierImag r q+defectImag r q+gradientImag r q k)*powerImag r k)/2

/-- Article: the complete initialized slack, including its fixed Y=2 scalar reserve. -/
def pairSlack (r q δ : ℝ) (k : ℕ) : ℝ :=
  radius r q k+δ*discrepancy r q k+(1-(-q^2)^((k+1)/2))^2

/-- Article: the source cosine polynomials satisfy their exact three-term recursion. -/
theorem chebT_rec (n : ℕ) (c : ℝ) :
    polyak.Spectral.chebT (n+2) c=
      2*c*polyak.Spectral.chebT (n+1) c-polyak.Spectral.chebT n c := by
  have hh := congrArg (Polynomial.eval c) (Polynomial.Chebyshev.T_add_two ℝ (n : ℤ))
  simpa only [polyak.Spectral.chebT,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,
    Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using hh

/-- Article: the source sine polynomials satisfy the same exact recursion. -/
theorem chebU_rec (n : ℕ) (c : ℝ) :
    polyak.Spectral.chebU (n+2) c=
      2*c*polyak.Spectral.chebU (n+1) c-polyak.Spectral.chebU n c := by
  have hh := congrArg (Polynomial.eval c) (Polynomial.Chebyshev.U_add_two ℝ (n : ℤ))
  simpa only [polyak.Spectral.chebU,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,
    Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X] using hh

end
end polyak.Realization.ExplicitSpiral.Source
