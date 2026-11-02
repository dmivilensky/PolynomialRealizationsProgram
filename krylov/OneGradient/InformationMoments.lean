import krylov.OneGradient.Information
import krylov.Reference.CGMomentInvariance
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(a).
Use: derive all fixed moments from the original physical Krylov information,
and isolate the actual first missing moment under a last-normal rank-one change.
Source: genuine operator powers, symmetric polynomial actions and the actual
one-gradient information flag; no moment equality is assumed as a fibre field.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Reference Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true physical moments of a normalized initial vector.
Use: connect information equality to the original gradient spectral moments.
Article: main_krylov, s5:moment(a).
Proof: pair the actual kth operator power with the input and normalize its energy. -/
def physicalMoment (Q : E →L[ℝ] E) (g : E) (k : ℕ) : ℝ :=
  inner ℝ g ((Q^k) g)/‖g‖^2

/-- The actual physical power vectors through the known Krylov action coincide.
Use: the observed restriction fixes vectors before any moment or CG argument.
Article: main_krylov, s5:moment(a).
Proof: each next action is on a genuine old Krylov vector, so the given physical
restriction applies before the unknown last curvature is used. -/
theorem information_power_vectors (Q C : E →L[ℝ] E) (g : E) (N : ℕ)
    (hact : ∀ v∈CG.krylovSpace Q g N,C v=Q v) (k : ℕ) (hk : k≤N) :
    (C^k) g=(Q^k) g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ',mul_apply_eq_comp,ih (by omega)]
    apply hact
    rw [krylov_space_powers]
    exact Submodule.subset_span ⟨k,show k<N by omega,rfl⟩

/-- The actual Krylov flags through the first unqueried vector coincide.
Use: transport old-flag decompositions to every physical completion, independently
of CG consistency or the candidate method's own choices.
Article: main_krylov, apE:info.
Proof: the power-vector dictionary identifies each genuine generator using
the already proved common known physical actions. -/
theorem information_krylov_space (Q C : E →L[ℝ] E) (g : E) (N : ℕ)
    (hact : ∀ v∈CG.krylovSpace Q g N,C v=Q v) (k : ℕ) (hk : k≤N+1) :
    CG.krylovSpace C g k=CG.krylovSpace Q g k := by
  rw [krylov_space_powers,krylov_space_powers]
  congr 1
  ext w
  constructor <;> rintro ⟨i,hi,rfl⟩
  · exact ⟨i,hi,(information_power_vectors Q C g N hact i (by change i<k at hi;omega)).symm⟩
  · exact ⟨i,hi,information_power_vectors Q C g N hact i (by change i<k at hi;omega)⟩

/-- A physical symmetric operator power is symmetric as an actual linear map.
Use: split the observed moment into two individually known physical power vectors.
Article: main_krylov, s5:moment(a).
Proof: the standard symmetric-linear-map power theorem applies to the actual
continuous operator through its underlying linear-map algebra homomorphism. -/
theorem symmetric_power (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (k : ℕ) :
    (Q^k).toLinearMap.IsSymmetric := by
  rw [ContinuousLinearMap.toLinearMap_pow]
  exact hQ.pow k

/-- A physical moment of order j+l is the inner product of the two actual power vectors.
Use: every moment through twice the known prefix length is already determined.
Article: main_krylov, s5:moment(a).
Proof: move the genuine symmetric power across the real inner product and
combine the actual commuting powers. -/
theorem moment_split (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (g : E) (j l : ℕ) :
    inner ℝ g ((Q^(j+l)) g)=inner ℝ ((Q^j) g) ((Q^l) g) := by
  have hs := symmetric_power Q hQ j
  have he := hs g ((Q^l) g)
  change inner ℝ ((Q^j) g) ((Q^l) g)=inner ℝ g ((Q^j) ((Q^l) g)) at he
  rw [pow_add,mul_apply_eq_comp]
  exact he.symm

/-- The original Krylov information fixes every actual normalized spectral
moment through order 2N, with all possible completions quantified explicitly.
Use: prove the fixed part of the missing-moment statement, without defining
the fibre by a presumed list of common moments.
Article: main_krylov, s5:moment(a).
Proof: split the kth symmetric physical moment into powers of orders at most N,
then use the proved equality of their actual vector actions. -/
theorem information_fixed_moments (Q C : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hC : C.toLinearMap.IsSymmetric)
    (g : E) (N : ℕ) (hact : ∀ v∈CG.krylovSpace Q g N,C v=Q v)
    (k : ℕ) (hk : k≤2*N) : physicalMoment C g k=physicalMoment Q g k := by
  let j := min k N
  let l := k-j
  have hj : j≤N := min_le_right _ _
  have hl : l≤N := by dsimp only [l,j];omega
  have hsum : k=j+l := by dsimp only [l,j];omega
  unfold physicalMoment
  rw [hsum,moment_split C hC,moment_split Q hQ,
    information_power_vectors Q C g N hact j hj,information_power_vectors Q C g N hact l hl]

/-- The first missing physical moment changes by exactly the square of the
actual last-normal power pairing times the free scalar pivot change.
Use: identify the genuine nonzero affine parameter before rewriting its
coefficient as the printed Jacobi coupling product.
Article: main_krylov, s5:moment(a).
Proof: the order-(2N+1) moment is the curvature of the common Nth power vector.
Insert the real rank-one completion and compute its actual quadratic form. -/
theorem information_first_missing_moment (Q C : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hC : C.toLinearMap.IsSymmetric)
    (g z : E) (N : ℕ) (t : ℝ)
    (hact : ∀ v∈CG.krylovSpace Q g N,C v=Q v)
    (hCform : C=Q+t • InnerProductSpace.rankOne ℝ z z) :
    physicalMoment C g (2*N+1)=physicalMoment Q g (2*N+1)+
      t*(inner ℝ z ((Q^N) g))^2/‖g‖^2 := by
  have hsC := moment_split C hC g N (N+1)
  have hsQ := moment_split Q hQ g N (N+1)
  have hexp : N+(N+1)=2*N+1 := by omega
  have hCs : (C^(N+1)) g=C ((C^N) g) := by rw [pow_succ',mul_apply_eq_comp]
  have hQs : (Q^(N+1)) g=Q ((Q^N) g) := by rw [pow_succ',mul_apply_eq_comp]
  rw [hexp,hCs,information_power_vectors Q C g N hact N le_rfl] at hsC
  rw [hexp,hQs] at hsQ
  unfold physicalMoment
  rw [hsC,hsQ,hCform]
  simp only [_root_.add_apply,_root_.smul_apply,InnerProductSpace.rankOne_apply,
    inner_add_right,real_inner_smul_right]
  rw [real_inner_comm ((Q^N) g) z]
  ring

end
end krylov.OneGradient
