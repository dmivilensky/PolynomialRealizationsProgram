import chebyshev1.SineJacobi.InteriorBounds
import chebyshev1.SineJacobi.Gain
import chebyshev1.Jacobi.OrderAttainment
import chebyshev1.Realization.StaticShiftGeneral

/-!
Article: chebyshev1, Corollary 5.3.
The same static example attains every homogeneous insertion order.
Result: `chebyshev1.SineJacobi.driftOrder_static_attained` supplies the stated article
conclusion.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Polynomial Polynomial.Chebyshev
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
The stated quantitative bound `opNorm (((data N).realization I).operatorTransfer N (fun s =>
H+E s) - aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Use: `chebyshev1.Nonlinear.MethodFamily.finiteDrift_le` uses this identity to establish the
stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N (fun s =>
H+E s) - aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Article: chebyshev1, Corollary 5.3.

Proof: Use the identities/estimates `chebyshev1.JacobiData.opNorm_finiteDrift_endpoint_le`,
`chebyshev1.SineJacobi.admissible`, `chebyshev1.SineJacobi.endpointMax` with the
arguments shown in the proof.
-/
theorem opNorm_finiteDrift_le (I : SpectralInterval) {N : ℕ} (hN : 0 < N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm (((data N).realization I).operatorTransfer N (fun s => H+E s) - aeval H (I.residual N)) ≤
      I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1) :=
  (data N).opNorm_finiteDrift_endpoint_le I (admissible I N hN)
    (endpointMax N hN) (terminal N hN) H hH hspec E delta hd hE
/--
The stated quantitative bound `opNorm (((data N).realization I).driftRemainder N H E) ≤
I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1-2*(N:ℝ)^2*delta/I.delta)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Corollary 5.3.

Proof: Use the identities/estimates
`chebyshev1.JacobiData.opNorm_driftRemainder_endpoint_le`,
`chebyshev1.SineJacobi.admissible`, `chebyshev1.SineJacobi.endpointMax` with the
arguments shown in the proof.
-/
theorem opNorm_driftRemainder_le (I : SpectralInterval) {N : ℕ} (hN : 0 < N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm (((data N).realization I).driftRemainder N H E) ≤
      I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1-2*(N:ℝ)^2*delta/I.delta) :=
  (data N).opNorm_driftRemainder_endpoint_le I hN (admissible I N hN)
    (endpointMax N hN) (terminal N hN) H hH hspec E delta hd hE
/--
The stated quantitative bound `opNorm (((data N).realization I).driftRemainder N H E) ≤
(2/3:ℝ)*I.epsilon N*(N:ℝ)^4*(delta/I.delta)^2 * Real.cosh (2*(N:ℝ)*Real.sqrt (delta/I.delta))`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Corollary 5.3.

Proof: Use the identities/estimates `chebyshev1.JacobiData.opNorm_driftRemainder_cosh_le`,
`chebyshev1.SineJacobi.admissible`, `chebyshev1.SineJacobi.endpointMax` with the
arguments shown in the proof.
-/
theorem opNorm_driftRemainder_cosh_le (I : SpectralInterval) {N : ℕ} (hN : 0 < N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm (((data N).realization I).driftRemainder N H E) ≤
      (2/3:ℝ)*I.epsilon N*(N:ℝ)^4*(delta/I.delta)^2 *
        Real.cosh (2*(N:ℝ)*Real.sqrt (delta/I.delta)) :=
  (data N).opNorm_driftRemainder_cosh_le I hN (admissible I N hN)
    (endpointMax N hN) (terminal N hN) H hH hspec E delta hd hE

/--
The stated quantitative bound `opNorm (((data N).realization I).linearResponse N H E) ≤
2*(N:ℝ)^2*I.epsilon N*delta/I.delta`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Corollary 5.3.

Proof: Use the identities/estimates
`chebyshev1.JacobiData.opNorm_linearResponse_endpoint_le`,
`chebyshev1.SineJacobi.admissible`, `chebyshev1.SineJacobi.endpointMax` with the
arguments shown in the proof.
-/
theorem opNorm_linearResponse_le (I : SpectralInterval) {N : ℕ} (hN : 0 < N)
    (H : Matrix d d ℝ) (hH : H.IsHermitian) (hspec : spectrum ℝ H ⊆ Set.Icc I.mu I.L)
    (E : ℕ → Matrix d d ℝ) (delta : ℝ) (hE : ∀ s < N, opNorm (E s) ≤ delta) :
    opNorm (((data N).realization I).linearResponse N H E) ≤
      2*(N:ℝ)^2*I.epsilon N*delta/I.delta :=
  (data N).opNorm_linearResponse_endpoint_le I (admissible I N hN) (endpointMax N hN)
    (residualPolynomial I N hN) H hH hspec E delta hE

/--
All orders have exactly the Chebyshev partition constants.

Exact identity `(data N).G N k = 2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Corollary 5.3.

Proof: Use the identities/estimates `chebyshev1.JacobiData.G_eq_chebyshev_coeff_all`,
`chebyshev1.SineJacobi.admissible`, `chebyshev1.SineJacobi.endpointMax` with the
arguments shown in the proof.
-/
theorem G_exact (I : SpectralInterval) {N k : ℕ} (hN : 0 < N) :
    (data N).G N k = 2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k :=
  (data N).G_eq_chebyshev_coeff_all I (admissible I N hN) (endpointMax N hN) (terminal N hN) k

/--
The three finite drift bounds are attained by the same static scalar example.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Corollary 5.3.

Proof: Use the identities/estimates `chebyshev1.Realization.static_shift_attained`,
`chebyshev1.SineJacobi.residualPolynomial` with the arguments shown in the proof.
-/
theorem static_shift_attained (I : SpectralInterval) {N : ℕ} (hN : 0 < N)
    (delta : ℝ) (hd : 0 ≤ delta) :
    opNorm (((data N).realization I).operatorTransfer N (fun _ => scalarMatrix (I.mu-delta)) -
      aeval (scalarMatrix I.mu) (I.residual N)) =
        I.epsilon N*((T ℝ N).eval (1+2*delta/I.delta)-1) ∧
    opNorm (((data N).realization I).linearResponse N (scalarMatrix I.mu)
      (fun _ => scalarMatrix (-delta))) = 2*(N:ℝ)^2*I.epsilon N*delta/I.delta ∧
    opNorm (((data N).realization I).driftRemainder N (scalarMatrix I.mu)
      (fun _ => scalarMatrix (-delta))) =
        I.epsilon N*((T ℝ N).eval (1+2*delta/I.delta)-1-2*(N:ℝ)^2*delta/I.delta) :=
  ((data N).realization I).static_shift_attained I N (residualPolynomial I N hN) delta hd


/--
The same static example attains every homogeneous insertion order.

Exact identity `opNorm ((data N).driftOrder I N k (scalarMatrix I.mu) (fun _ => scalarMatrix
(-delta))) = I.epsilon N*(2*delta/I.delta)^k*(taylor 1 (T ℝ N)).coeff k`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Corollary 5.3.

Proof: Use the identities/estimates `chebyshev1.JacobiData.opNorm_driftOrder_static`,
`chebyshev1.SineJacobi.admissible`, `chebyshev1.SineJacobi.endpointMax` with the
arguments shown in the proof.
-/
theorem driftOrder_static_attained (I : SpectralInterval) {N : ℕ} (hN : 0 < N)
    (k : ℕ) (delta : ℝ) (hd : 0 ≤ delta) :
    opNorm ((data N).driftOrder I N k (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta))) =
      I.epsilon N*(2*delta/I.delta)^k*(taylor 1 (T ℝ N)).coeff k :=
  (data N).opNorm_driftOrder_static I (admissible I N hN) (endpointMax N hN) (terminal N hN) k delta hd

end
end chebyshev1.SineJacobi
