import jacobi.Analysis.QuadraticError

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
A genuine finite quadratic lower bound controls solutions of the actual
row linear system, uniformly in the growing block size. This supplies
the inverse estimate needed for the original Cholesky rows without a
choice of matrix norm convention.
Source: finite Cauchy--Schwarz and coercivity.
Use: the actual Cholesky coefficient rows and their residual comparison rows inherit the proved dimension-independent principal Gram bound.
-/
namespace jacobi.Analysis
noncomputable section

/-- The solution of a genuinely coercive finite row system has the
Euclidean bound ||c||_2<=||b||_2/kappa, written without square roots.
Use: the actual Cholesky coefficient rows and their residual comparison
rows inherit the proved dimension-independent principal Gram bound.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Source: Cauchy--Schwarz for coercive finite systems.
Proof: test the actual row equation against its own solution. The
quadratic gap bounds this scalar from below; finite Cauchy--Schwarz
bounds its square from above. Cancel the nonzero solution norm; the
zero solution is handled separately. -/
theorem coercive_row_system {ι:Type*} [Fintype ι]
    (A:ι→ι→ℝ) {κ:ℝ} (hκ:0<κ)
    (hA:∀v:ι→ℝ, κ*(∑ i, (v i)^2)≤∑ i,∑ j, A i j*v i*v j)
    (c b:ι→ℝ) (he:∀j, (∑ i, c i*A i j)=b j) :
    κ^2*(∑ i, (c i)^2)≤∑ i, (b i)^2 := by
  -- Testing the genuine system against its solution exposes the coercive quadratic form.
  let S : ℝ := ∑ i, (c i)^2
  let T : ℝ := ∑ i, (b i)^2
  let d : ℝ := ∑ i, c i*b i
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hT : 0≤T := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hform : (∑ i,∑ j, A i j*c i*c j)=d := by
    rw [Finset.sum_comm]
    dsimp [d]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul]
    have hh : (∑ i, A i j*c i)=b j := by simpa only [mul_comm] using he j
    rw [hh,mul_comm]
  have hl : κ*S≤d := by simpa only [hform] using hA c
  have hd : 0≤d := (mul_nonneg hκ.le hS).trans hl
  have hcs : d^2≤S*T := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c b
  have hsquare : (κ*S)^2≤d^2 := sq_le_sq₀ (mul_nonneg hκ.le hS) hd |>.mpr hl
  by_cases hz : S=0
  · change κ^2*S≤T
    rw [hz,mul_zero]
    exact hT
  · have hp : 0<S := lt_of_le_of_ne hS (Ne.symm hz)
    change κ^2*S≤T
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith

/-- A coercive row system with O(1/N) forcing has a uniform absolute
coordinate-sum bound when its dimension is at most N.
Use: the original Cholesky row equation then gives O(1/N) for every
individual coefficient and for the original Schur normalization error.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: test the genuine system against its solution and bound the
forcing by its actual coordinate maximum. Finite Cauchy--Schwarz bounds
the squared absolute coordinate sum by N times the squared norm.
Cancel the nonzero absolute coordinate sum; the zero case is immediate. -/
theorem coercive_row_l1 {ι:Type*} [Fintype ι]
    (A:ι→ι→ℝ) {κ C N:ℝ} (hκ:0<κ) (hC:0≤C) (hN:0<N)
    (hdim:(Fintype.card ι:ℝ)≤N)
    (hA:∀v:ι→ℝ, κ*(∑ i, (v i)^2)≤∑ i,∑ j, A i j*v i*v j)
    (c b:ι→ℝ) (he:∀j, (∑ i, c i*A i j)=b j)
    (hb:∀j, |b j|≤C/N) : (∑ i, |c i|)≤C/κ := by
  -- The forcing bound and the finite dimension bound control the same absolute coordinate mass.
  let S : ℝ := ∑ i, (c i)^2
  let L : ℝ := ∑ i, |c i|
  have hS : 0≤S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hL : 0≤L := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hform : (∑ i,∑ j, A i j*c i*c j)=∑ j, c j*b j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul]
    have hh : (∑ i, A i j*c i)=b j := by simpa only [mul_comm] using he j
    rw [hh,mul_comm]
  have hforce : (∑ j, c j*b j)≤(C/N)*L := by
    calc
      _ ≤ ∑ j, |c j| * (C/N) := Finset.sum_le_sum (fun j _ =>
        (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb j) (abs_nonneg _)))
      _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _
  have henergy : κ*S≤(C/N)*L := by
    have hh := hA c
    rw [hform] at hh
    exact hh.trans hforce
  have hcs : L^2≤N*S := (sum_abs_sq_le c).trans (mul_le_mul_of_nonneg_right hdim hS)
  have hprod : κ*L^2≤C*L := by
    calc
      _ ≤ κ*(N*S) := mul_le_mul_of_nonneg_left hcs hκ.le
      _ = N*(κ*S) := by ring
      _ ≤ N*((C/N)*L) := mul_le_mul_of_nonneg_left henergy hN.le
      _ = C*L := by field_simp
  apply (le_div_iff₀ hκ).mpr
  by_cases hz : L=0
  · change L*κ≤C
    rw [hz,zero_mul]
    exact hC
  · have hp : 0<L := lt_of_le_of_ne hL (Ne.symm hz)
    change L*κ≤C
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith

/-- The actual maximum of scaled forcing coordinates controls every
finite coefficient-weighted sum by its absolute coefficient mass.
Use: quantitative Cholesky bounds estimate each original row equation
and its exact Schur normalization with one common matrix-entry bound.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: take the absolute finite sum, distribute its nonnegative scale
and apply the genuine bound to every original forcing coordinate. -/
theorem scaled_sum_mul_bound {ι:Type*} [Fintype ι] (c b:ι→ℝ)
    {N C:ℝ} (hN:0≤N) (hb:∀i, N*|b i|≤C) :
    N*|∑ i, c i*b i|≤C*(∑ i, |c i|) := by
  -- Distribute the nonnegative scale after the absolute finite-sum bound.
  calc
    _ ≤ N*∑ i, |c i*b i| := mul_le_mul_of_nonneg_left
      (Finset.abs_sum_le_sum_abs _ _) hN
    _ = ∑ i, |c i| * (N*|b i|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul]
      ring
    _ ≤ ∑ i, C*|c i| := Finset.sum_le_sum (fun i _ => by
      have hh := mul_le_mul_of_nonneg_left (hb i) (abs_nonneg (c i))
      simpa only [mul_comm C] using hh)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- A coercive identity perturbation with O(1/N) entries has a uniform
inverse bound in coordinate maximum norm, even on growing finite blocks.
Use: the genuine Cholesky residual equation turns a uniform vanishing
GL quadrature error into uniform convergence of the actual coefficients.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the actual row solution has absolute mass at most N*epsilon/kappa
by the proved coercive-system estimate. Its identity-plus-perturbation
equation isolates each coordinate. The perturbation contributes at most
C/N times that genuine mass, giving (1+C/kappa)*epsilon. -/
theorem coercive_row_sup {ι:Type*} [Fintype ι] [DecidableEq ι]
    (E:ι→ι→ℝ) {κ C N:ℝ} (hκ:0<κ) (hC:0≤C) (hN:0<N)
    (hdim:(Fintype.card ι:ℝ)≤N)
    (hA:∀v:ι→ℝ, κ*(∑ i, (v i)^2)≤
      ∑ i,∑ j, ((if i=j then (1:ℝ) else 0)+E i j)*v i*v j)
    (hE:∀i j, N*|E i j|≤C)
    (c b:ι→ℝ) (he:∀j, c j+(∑ i, c i*E i j)=b j)
    {ε:ℝ} (hε:0≤ε) (hb:∀j, |b j|≤ε) :
    ∀ j, |c j|≤(1+C/κ)*ε := by
  -- First bound the total coefficient mass; the identity term then isolates each coordinate.
  have hsys (j:ι) : (∑ i, c i*((if i=j then (1:ℝ) else 0)+E i j))=b j := by
    simp only [mul_add,Finset.sum_add_distrib,mul_ite,mul_one,mul_zero,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact he j
  have hl1 : (∑ i, |c i|)≤(N*ε)/κ := coercive_row_l1
    (fun i j => (if i=j then (1:ℝ) else 0)+E i j) hκ (mul_nonneg hN.le hε) hN
    hdim hA c b hsys (fun j => by simpa only [mul_div_cancel_left₀ ε hN.ne'] using hb j)
  intro j
  have hsum := (scaled_sum_mul_bound c (fun i => E i j) hN.le (fun i => hE i j)).trans
    (mul_le_mul_of_nonneg_left hl1 hC)
  have hsum' : |∑ i, c i*E i j|≤(C/κ)*ε := by
    apply (mul_le_mul_iff_right₀ hN).mp
    have heq : C*(N*ε/κ)=((C/κ)*ε)*N := by ring
    rw [heq] at hsum
    nlinarith
  have hc : c j=b j-(∑ i, c i*E i j) := by linarith [he j]
  rw [hc]
  have hh := abs_sub_le (b j) 0 (∑ i, c i*E i j)
  simp only [sub_zero,zero_sub,abs_neg] at hh
  exact hh.trans (by nlinarith [hb j])

end
end jacobi.Analysis
