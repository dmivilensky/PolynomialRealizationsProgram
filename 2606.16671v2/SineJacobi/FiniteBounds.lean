import «2606.16671v2».SineJacobi.InteriorBounds
import «2606.16671v2».SineJacobi.Gain
import «2606.16671v2».Jacobi.OrderAttainment
import «2606.16671v2».Realization.StaticShiftGeneral

/-!
Article: 2606.16671v2, Corollary 5.3.
The same static example attains every homogeneous insertion order.
Result: `«2606.16671v2».SineJacobi.driftOrder_static_attained` supplies the stated article
conclusion.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Polynomial Polynomial.Chebyshev
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
The stated quantitative bound `opNorm (((data N).realization I).operatorTransfer N (fun s =>
H+E s) - aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Use: `«2606.16671v2».Nonlinear.MethodFamily.finiteDrift_le` uses this identity to establish the
stated quantitative bound `opNorm (((family.data N).realization I).operatorTransfer N (fun s =>
H+E s) - aeval H (I.residual N)) ≤ I.epsilon N * ((T ℝ N).eval (1+2*delta/I.delta)-1)`.

Article: 2606.16671v2, Corollary 5.3.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.opNorm_finiteDrift_endpoint_le`,
`«2606.16671v2».SineJacobi.admissible`, `«2606.16671v2».SineJacobi.endpointMax` with the
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

Article: 2606.16671v2, Corollary 5.3.

Proof: Use the identities/estimates
`«2606.16671v2».JacobiData.opNorm_driftRemainder_endpoint_le`,
`«2606.16671v2».SineJacobi.admissible`, `«2606.16671v2».SineJacobi.endpointMax` with the
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

Article: 2606.16671v2, Corollary 5.3.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.opNorm_driftRemainder_cosh_le`,
`«2606.16671v2».SineJacobi.admissible`, `«2606.16671v2».SineJacobi.endpointMax` with the
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

Article: 2606.16671v2, Corollary 5.3.

Proof: Use the identities/estimates
`«2606.16671v2».JacobiData.opNorm_linearResponse_endpoint_le`,
`«2606.16671v2».SineJacobi.admissible`, `«2606.16671v2».SineJacobi.endpointMax` with the
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

Article: 2606.16671v2, Corollary 5.3.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.G_eq_chebyshev_coeff_all`,
`«2606.16671v2».SineJacobi.admissible`, `«2606.16671v2».SineJacobi.endpointMax` with the
arguments shown in the proof.
-/
theorem G_exact (I : SpectralInterval) {N k : ℕ} (hN : 0 < N) :
    (data N).G N k = 2/(2:ℝ)^k*(taylor 1 (T ℝ N)).coeff k :=
  (data N).G_eq_chebyshev_coeff_all I (admissible I N hN) (endpointMax N hN) (terminal N hN) k

/--
The three finite drift bounds are attained by the same static scalar example.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2606.16671v2, Corollary 5.3.

Proof: Use the identities/estimates `«2606.16671v2».Realization.static_shift_attained`,
`«2606.16671v2».SineJacobi.residualPolynomial` with the arguments shown in the proof.
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

Article: 2606.16671v2, Corollary 5.3.

Proof: Use the identities/estimates `«2606.16671v2».JacobiData.opNorm_driftOrder_static`,
`«2606.16671v2».SineJacobi.admissible`, `«2606.16671v2».SineJacobi.endpointMax` with the
arguments shown in the proof.
-/
theorem driftOrder_static_attained (I : SpectralInterval) {N : ℕ} (hN : 0 < N)
    (k : ℕ) (delta : ℝ) (hd : 0 ≤ delta) :
    opNorm ((data N).driftOrder I N k (scalarMatrix I.mu) (fun _ => scalarMatrix (-delta))) =
      I.epsilon N*(2*delta/I.delta)^k*(taylor 1 (T ℝ N)).coeff k :=
  (data N).opNorm_driftOrder_static I (admissible I N hN) (endpointMax N hN) (terminal N hN) k delta hd

end
end «2606.16671v2».SineJacobi
