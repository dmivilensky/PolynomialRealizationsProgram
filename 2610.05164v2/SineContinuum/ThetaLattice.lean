import Mathlib.Data.Int.DivMod
import Mathlib.Tactic

/-!
Article: 2610.05164v2, Proposition 2.
Rotation preserves the Gaussian quadratic form with the two half-shift sectors.
Use: `«2610.05164v2».SineContinuum.thetaLattice` feeds
`«2610.05164v2».SineContinuum.thetaFour_duplication` (The signed theta duplication identity, proved
by the same lattice bijection).
Proof chain: `«2610.05164v2».LocalObstruction.sine_green_scale_tail` — 2610.05164v2, Theorem 6.1; No
locally sharp C1 bound from finitely many spectral observations.
Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities. The needed form is proved here.
-/
namespace «2610.05164v2».SineContinuum

/--
The even/odd rotation of the integer lattice used in theta duplication.

Use: `«2610.05164v2».SineContinuum.thetaLattice_half_square` uses this definition to establish
exact identity `(((thetaLattice p).1:ℝ)+1/2)^2+(((thetaLattice p).2:ℝ)+1/2)^2 =
2*((p.2.1:ℝ)+((p.1.val:ℝ)+1)/2)^2+2*((p.2.2:ℝ)+(p.1.val:ℝ)/2)^2`.

Article: 2610.05164v2, Proposition 2 via `«2610.05164v2».SineContinuum.n_theta`.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.
-/
def thetaLattice : (Fin 2 × ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.2.1+p.2.2+(p.1.val:ℤ),p.2.1-p.2.2)
  invFun p := (⟨(p.1+p.2)%2 |>.toNat,by omega⟩,(p.1+p.2)/2,(p.1-p.2)/2)
  left_inv p := by
    obtain ⟨r,u,v⟩ := p
    apply Prod.ext
    · apply Fin.ext
      simp only
      have hr := r.isLt
      omega
    · apply Prod.ext <;> simp only <;> have hr := r.isLt <;> omega
  right_inv p := by
    obtain ⟨m,n⟩ := p
    apply Prod.ext <;> simp only <;> omega

/--
Rotation preserves the Gaussian quadratic form with the two half-shift sectors.

Exact identity `((thetaLattice p).1:ℝ)^2+((thetaLattice p).2:ℝ)^2 =
2*((p.2.1:ℝ)+(p.1.val:ℝ)/2)^2+2*((p.2.2:ℝ)+(p.1.val:ℝ)/2)^2`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 2.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem thetaLattice_square (p : Fin 2 × ℤ × ℤ) :
    ((thetaLattice p).1:ℝ)^2+((thetaLattice p).2:ℝ)^2 =
      2*((p.2.1:ℝ)+(p.1.val:ℝ)/2)^2+2*((p.2.2:ℝ)+(p.1.val:ℝ)/2)^2 := by
  change (((p.2.1+p.2.2+(p.1.val:ℤ)):ℤ):ℝ)^2+((p.2.1-p.2.2:ℤ):ℝ)^2 = _
  push_cast
  ring

/--
Exact identity `(((thetaLattice p).1:ℝ)+1/2)^2+(((thetaLattice p).2:ℝ)+1/2)^2 =
2*((p.2.1:ℝ)+((p.1.val:ℝ)+1)/2)^2+2*((p.2.2:ℝ)+(p.1.val:ℝ)/2)^2`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 2.

Source: Stein and Shakarchi, Fourier Analysis; NIST Digital Library of Mathematical Functions,
Chapter 20 — Poisson summation and Jacobi theta identities.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem thetaLattice_half_square (p : Fin 2 × ℤ × ℤ) :
    (((thetaLattice p).1:ℝ)+1/2)^2+(((thetaLattice p).2:ℝ)+1/2)^2 =
      2*((p.2.1:ℝ)+((p.1.val:ℝ)+1)/2)^2+2*((p.2.2:ℝ)+(p.1.val:ℝ)/2)^2 := by
  change ((((p.2.1+p.2.2+(p.1.val:ℤ)):ℤ):ℝ)+1/2)^2+(((p.2.1-p.2.2:ℤ):ℝ)+1/2)^2 = _
  push_cast
  ring

end «2610.05164v2».SineContinuum
