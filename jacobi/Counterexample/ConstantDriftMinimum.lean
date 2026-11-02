import jacobi.Counterexample.ConstantDriftGreen

/-!
Article: jacobi, Proposition 6.1.
The explicit original Jacobi chain attains the exact minimum
n*H^2/kappa^2 over its complete original positive-coupling isospectral
fibre. Every competitor has the same actual resolvent trace, and the
earlier finite Cauchy--Schwarz bound is sharp at the constructed constant
Green diagonal. No attainment or minimum certificate is assumed.
Use: constantDriftChain_minimum realizes the claimed minimum with this explicitly constructed original fibre member.
-/
namespace jacobi.Counterexample
noncomputable section
open Matrix jacobi.Finite chebyshev2
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The source's actual attaining chain has the exact printed finite resolvent energy.
Use: constantDriftChain_minimum realizes the claimed minimum with this explicitly constructed original fibre member.
Article: jacobi, Proposition 6.1.
Proof: its independently proved true Green diagonal is H/kappa in
every original physical row. Sum the N identical squared entries. -/
theorem constantDriftChain_energy {N:ℕ} (d l:ℕ→ℝ) {kappa H:ℝ}
    (hk:0<kappa) (hH:0<H) (hl:l 0=0) (hdiag:∀i<N,0<d i)
    (hlower:∀ i, 0 < i → i < N → 0 < l i) (hd:∀i<N,(d i)^2-(l i)^2=kappa) :
    (constantDriftChain d l N H).energy=(N:ℝ)*H^2/kappa^2 := by
  simp only [Jacobi.energy,constantDriftChain_diagonal d l hk hH hl hdiag hlower hd,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- The original attaining chain has the exact printed complete resolvent trace.
Use: constantDriftChain_minimum transfers this same trace to every original fibre competitor through the unchanged characteristic polynomial.
Article: jacobi, Proposition 6.1.
Proof: sum its proved actual constant Green diagonal H/kappa. -/
theorem constantDriftChain_trace {N:ℕ} (d l:ℕ→ℝ) {kappa H:ℝ}
    (hk:0<kappa) (hH:0<H) (hl:l 0=0) (hdiag:∀i<N,0<d i)
    (hlower:∀ i, 0 < i → i < N → 0 < l i) (hd:∀i<N,(d i)^2-(l i)^2=kappa) :
    Matrix.trace (constantDriftChain d l N H).green=(N:ℝ)*(H/kappa) := by
  simp only [Matrix.trace,Matrix.diag_apply,constantDriftChain_diagonal d l hk hH hl hdiag hlower hd,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

/-- The constructed actual chain attains the exact energy minimum over every member of its complete original isospectral fibre.
Use: the Laguerre family in Proposition 6.1 applies this theorem with its actual factor drift a+1 and original scale H_n.
Article: jacobi, Proposition 6.1.
Proof: the actual constructed chain is irreducible and its true energy
has the stated value. Its characteristic polynomial is nonzero at one.
Every original fibre competitor has that same polynomial, hence the
same true resolvent trace n*H/kappa. Finite Cauchy--Schwarz gives the
common lower bound, attained by the constructed constant diagonal. -/
theorem constantDriftChain_minimum {N:ℕ} (hN:0<N) (d l:ℕ→ℝ) {kappa H:ℝ}
    (hk:0<kappa) (hH:0<H) (hl:l 0=0) (hdiag:∀i<N,0<d i)
    (hlower:∀ i, 0 < i → i < N → 0 < l i) (hd:∀i<N,(d i)^2-(l i)^2=kappa) :
    InFiber (constantDriftChain d l N H) (constantDriftChain d l N H).matrix.charpoly ∧
    (constantDriftChain d l N H).energy=(N:ℝ)*H^2/kappa^2 ∧
    ∀J:Jacobi N,InFiber J (constantDriftChain d l N H).matrix.charpoly →
      (N:ℝ)*H^2/kappa^2≤J.energy := by
  -- The lower bound quantifies over the complete original fibre, with no symmetry or constant-diagonal restriction on competitors.
  refine ⟨⟨constantDriftChain_irreducible d l hH hdiag hlower,rfl⟩,
    constantDriftChain_energy d l hk hH hl hdiag hlower hd,fun J hJ=>?_⟩
  have hp := constantDriftChain_endpoint_ne d l hk hH hdiag hlower hd
  have hpJ : J.matrix.charpoly.eval 1≠0 := by rw [hJ.2]; exact hp
  have htrace : Matrix.trace J.green=Matrix.trace (constantDriftChain d l N H).green := by
    rw [green_trace J hpJ,green_trace _ hp,hJ.2]
  have hCS := trace_sq_le_energy J
  rw [htrace,constantDriftChain_trace d l hk hH hl hdiag hlower hd] at hCS
  have he : ((N:ℝ)*(H/kappa))^2=(N:ℝ)*((N:ℝ)*H^2/kappa^2) := by ring
  rw [he] at hCS
  exact (mul_le_mul_iff_right₀ (Nat.cast_pos.mpr hN)).mp hCS

end
end jacobi.Counterexample
