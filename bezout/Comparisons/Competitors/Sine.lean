import bezout.Comparisons.Competitors.TwoTerm
import chebyshev1.SineJacobi.Algorithm
import bezout.Gains.Spectral

/-!
Article: bezout, sine--Jacobi competitor and Equation `eq:competitor-sine`.
Use: the printed normalized Jacobi ratios give an actual current-query momentum
history, with the prescribed terminal and the established physical sine kernel.
Proof: positive Jacobi denominators justify every ratio; the generic two-term
bridge transfers the exact execution and its full spectral gain.
-/

namespace bezout.Comparisons.Competitors.Sine
noncomputable section
open chebyshev1 Polynomial
open scoped BigOperators

/-- Literal sine--Jacobi momentum parameters. -/
def config (I : SpectralInterval) (N : ℕ) : Momentum := TwoTerm.config ((SineJacobi.data N).method I)

/-- The actual N-call sine--Jacobi causal history. -/
def history (I : SpectralInterval) (N : ℕ) : bezout.History N := (config I N).history N

/-- The positive normalization ratio used by the printed scalar preparation. -/
def ratio (I : SpectralInterval) (N s : ℕ) : ℝ :=
  (SineJacobi.data N).den I s/(SineJacobi.data N).den I (s-1)

/-- Every ratio actually used by a physical call is positive. -/
theorem ratio_pos (I : SpectralInterval) (N : ℕ) (hN : 0<N) (s : ℕ) (hs : s≤N) :
    0<ratio I N s :=
  div_pos (SineJacobi.admissible I N hN s hs)
    (SineJacobi.admissible I N hN (s-1) (by omega))

/-- The scalar preparation starts at r_1=eta. -/
theorem ratio_one (I : SpectralInterval) (N : ℕ) : ratio I N 1=I.eta := by
  simp [ratio,JacobiData.den_one,SineJacobi.data_b]

/-- The actual two-term method preserves its fixed point at every used later step. -/
theorem fixed_point (I : SpectralInterval) (N : ℕ) (hN : 0<N)
    (s : ℕ) (hs : 0<s) (hsN : s<N) :
    ((SineJacobi.data N).method I).a s+((SineJacobi.data N).method I).b s=1 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s≠0)
  exact (SineJacobi.data N).fixed_point I n
    (ne_of_gt (SineJacobi.admissible I N hN (n+2) (by omega)))

/-- The printed scalar ratio recursion, with exactly the sine coupling c_s. -/
theorem ratio_step (I : SpectralInterval) (N : ℕ) (hN : 0<N)
    (s : ℕ) (hs : 0<s) (hsN : s<N) :
    ratio I N (s+1)=I.eta-SineJacobi.couplingSq N s/ratio I N s := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s≠0)
  have hr := (SineJacobi.data N).den_add_two I n
  simp only [SineJacobi.data_b,sub_zero,SineJacobi.data_aSq N (n+1) (by omega) hsN] at hr
  have hd0 := ne_of_gt (SineJacobi.admissible I N hN n (by omega))
  have hd1 := ne_of_gt (SineJacobi.admissible I N hN (n+1) (by omega))
  unfold ratio
  simp only [Nat.succ_sub_one]
  field_simp
  linear_combination hr

/-- The separately prescribed initial gradient step agrees with Prefix. -/
theorem initial_coefficients (I : SpectralInterval) (N : ℕ) :
    (config I N).alpha 0=2/(I.L+I.mu) ∧ (config I N).beta 0=0 := by
  exact ⟨(SineJacobi.method_initial I N).2.2,rfl⟩

/-- The displayed alpha and beta are exactly the normalized Jacobi coefficients. -/
theorem coefficients (I : SpectralInterval) (N : ℕ) (hN : 0<N)
    (s : ℕ) (hs : 0<s) (hsN : s<N) :
    (config I N).alpha s=2/(I.delta*ratio I N (s+1)) ∧
      (config I N).beta s=SineJacobi.couplingSq N s/(ratio I N s*ratio I N (s+1)) := by
  have hc := SineJacobi.method_coefficients I N s hs hsN
  have h0 := ne_of_gt (SineJacobi.admissible I N hN (s-1) (by omega))
  have h1 := ne_of_gt (SineJacobi.admissible I N hN s hsN.le)
  have h2 := ne_of_gt (SineJacobi.admissible I N hN (s+1) (by omega))
  change ((SineJacobi.data N).method I).gamma s=_ ∧
    (if s=0 then 0 else -((SineJacobi.data N).method I).b s)=_
  rw [hc.2.2,ite_eq_right (by omega),hc.2.1]
  unfold ratio
  simp only [Nat.add_sub_cancel]
  constructor <;> field_simp

/-- Exact terminal of the actual physical sine--Jacobi algorithm. -/
theorem terminal (I : SpectralInterval) (N : ℕ) (hN : 0<N) :
    (history I N).terminal=I.residual N := by
  rw [history,config,TwoTerm.terminal _ N (fixed_point I N hN),
    ← JacobiData.realization,SineJacobi.residualPolynomial I N hN]

/-- The actual physical kernel is exactly the established sine--Jacobi kernel. -/
theorem realization_kernel (I : SpectralInterval) (N : ℕ) (hN : 0<N)
    (s : Fin N) (x y : ℝ) :
    (history I N).realization.kernel N s.val x y=((SineJacobi.data N).realization I).kernel N s.val x y :=
  TwoTerm.realization_kernel _ N (fixed_point I N hN) s x y

/-- The spectral gain of this actual history equals the established sine--Jacobi gain. -/
theorem gain_eq (I : SpectralInterval) (N : ℕ) (hN : 0<N) :
    (history I N).spectralGain I=((SineJacobi.data N).realization I).gain I N := by
  have hk (x y : ℝ) : (history I N).realization.kernelNorm N x y=
      ((SineJacobi.data N).realization I).kernelNorm N x y := by
    unfold Realization.kernelNorm
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    rw [realization_kernel I N hN ⟨s,Finset.mem_range.mp hs⟩]
  unfold bezout.History.spectralGain Realization.gain Realization.gainValues
  simp_rw [hk]

/-- Every actual endpoint physical product has the required common negative sign. -/
theorem kernel_mu (I : SpectralInterval) (N : ℕ) (hN : 0<N) (s : Fin N) :
    bezout.Lower.physicalKernel (history I N) s I.mu I.mu =
      -(2*I.epsilon N/I.delta)*SineJacobi.greenWeight N s.val := by
  change ((history I N).response s).eval I.mu * ((history I N).query s).eval I.mu = _
  rw [← bezout.History.realization_kernel,realization_kernel I N hN,SineJacobi.kernel_endpoint I N s.val s.isLt]

/-- Each endpoint product is strictly negative, without selecting signs call by call. -/
theorem kernel_mu_neg (I : SpectralInterval) (N : ℕ) (hN : 0<N) (s : Fin N) :
    bezout.Lower.physicalKernel (history I N) s I.mu I.mu<0 := by
  rw [kernel_mu I N hN]
  have hp := mul_pos (SineJacobi.endpoint_pos N s.val s.isLt)
    (SineJacobi.endpoint_pos N (N-s.val-1) (by omega))
  have he : 0<2*I.epsilon N/I.delta := by have := I.den_pos N; have := I.delta_pos; unfold SpectralInterval.epsilon; positivity
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos he) hp

/-- Every actual physical output is the sine history output, for arbitrary oracle errors. -/
theorem output_eq_history {E : Type*} [AddCommGroup E] [Module ℝ E]
    (I : SpectralInterval) (N : ℕ) (oracle : Fin N → E → E) (initial : E) :
    ((config I N).program N).output oracle initial=(history I N).oracleOutput initial oracle :=
  Momentum.output_eq_history _ _ _ _

end
end bezout.Comparisons.Competitors.Sine
