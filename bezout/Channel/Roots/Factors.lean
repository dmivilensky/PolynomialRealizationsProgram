import bezout.Channel.Roots.Permutation
import bezout.Synthesis.Normalized

/-!
Article: bezout, the LF/fractal configuration and Proposition D.1.
Use: constructs the actual positive reciprocal Chebyshev-root steps and proves
their full terminal polynomial, for every root ordering and every horizon.
Proof: explicit interior simple roots, N affine factors, and normalization at
zero identify the polynomial at N+1 distinct real points.
-/

namespace bezout.Channel.Roots
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- Canonical Chebyshev-root angle, indexed from zero. -/
def angle (N : ℕ) (s : Fin N) : ℝ := (2*(s.val:ℝ)+1)*Real.pi/(2*(N:ℝ))

/-- The physical root of the normalized terminal polynomial. -/
def node (I : chebyshev1.SpectralInterval) (N : ℕ) (s : Fin N) : ℝ :=
  (I.L+I.mu)/2-I.delta/2*Real.cos (angle N s)

/-- Positive reciprocal root steps in an arbitrary actual call ordering. -/
def steps (I : chebyshev1.SpectralInterval) (N : ℕ) (e : Equiv.Perm (Fin N))
    (s : Fin N) : ℝ := 1/node I N (e s)

/-- A natural-index schedule with the finite horizon extended by zero. -/
def schedule (I : chebyshev1.SpectralInterval) (N : ℕ) (e : Equiv.Perm (Fin N))
    (s : ℕ) : ℝ := if hs : s<N then steps I N e ⟨s,hs⟩ else 0

/-- Each root angle is strictly inside the half-circle. -/
theorem angle_mem (N : ℕ) (s : Fin N) : angle N s ∈ Set.Ioo 0 Real.pi := by
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by have := s.isLt; omega)
  have hs : (s.val:ℝ)<N := by exact_mod_cast s.isLt
  have hs' : (s.val:ℝ)+1≤N := by exact_mod_cast (show s.val+1≤N from s.isLt)
  unfold angle
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : 0<2*(N:ℝ))).mpr
    nlinarith [Real.pi_pos]

/-- The canonical cosine roots lie strictly between the two chart endpoints. -/
theorem cos_angle_mem (N : ℕ) (s : Fin N) : Real.cos (angle N s) ∈ Set.Ioo (-1) 1 := by
  have ht := angle_mem N s
  have h0 := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0) ht.2.le ht.1
  have hp := Real.cos_lt_cos_of_nonneg_of_le_pi ht.1.le (le_refl Real.pi) ht.2
  simpa only [Real.cos_zero, Real.cos_pi, Set.mem_Ioo] using And.intro hp h0

/-- Every reciprocal-root denominator lies strictly inside the physical spectral interval. -/
theorem node_mem (I : chebyshev1.SpectralInterval) (N : ℕ) (s : Fin N) :
    node I N s ∈ Set.Ioo I.mu I.L := by
  have ht := cos_angle_mem N s
  have hd := I.delta_pos
  have h1 := mul_pos hd (sub_pos.mpr ht.2)
  have h2 := mul_pos hd (show 0<1+Real.cos (angle N s) by linarith [ht.1])
  unfold node
  unfold chebyshev1.SpectralInterval.delta at *
  constructor <;> nlinarith

/-- Every actual root step is strictly positive. -/
theorem steps_pos (I : chebyshev1.SpectralInterval) (N : ℕ) (e : Equiv.Perm (Fin N))
    (s : Fin N) : 0<steps I N e s :=
  one_div_pos.mpr (I.mu_pos.trans (node_mem I N (e s)).1)

/-- The physical chart sends each root back to its exact cosine node. -/
theorem z_node (I : chebyshev1.SpectralInterval) (N : ℕ) (s : Fin N) :
    I.z (node I N s) = Real.cos (angle N s) := by
  unfold node chebyshev1.SpectralInterval.z
  have hd := ne_of_gt I.delta_pos
  field_simp
  ring

/-- Each constructed physical root annihilates the exact normalized terminal. -/
theorem residual_node (I : chebyshev1.SpectralInterval) (N : ℕ) (s : Fin N) :
    (I.residual N).eval (node I N s)=0 := by
  have hr : (T ℝ N).IsRoot (Real.cos (angle N s)) := by
    rw [← mem_roots (T_ne_zero ℝ N), roots_T_real]
    simp only [Finset.mem_val, Finset.mem_image, Finset.mem_range]
    refine ⟨s.val,s.isLt,?_⟩
    rfl
  rw [I.residual_eval, z_node, show (T ℝ N).eval (Real.cos (angle N s))=0 from hr, zero_div]

/-- Canonically ordered physical roots are strictly increasing and therefore distinct. -/
theorem node_strictMono (I : chebyshev1.SpectralInterval) (N : ℕ) : StrictMono (node I N) := by
  intro i j hij
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by have := i.isLt; omega)
  have hs : (i.val:ℝ)<j.val := by exact_mod_cast hij
  have ha : angle N i < angle N j := by
    unfold angle
    apply (div_lt_div_iff_of_pos_right (by positivity : 0<2*(N:ℝ))).mpr
    nlinarith [Real.pi_pos]
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (angle_mem N i).1.le (angle_mem N j).2.le ha
  have hp := mul_pos I.delta_pos (sub_pos.mpr hc)
  unfold node
  nlinarith

/-- Terminal product of the literal scalar gradient steps. -/
def terminal {N : ℕ} (α : Fin N → ℝ) : ℝ[X] := ∏ s, (1-C (α s)*X)

/-- No permutation changes the nominal polynomial of a root-step schedule. -/
theorem terminal_permute {N : ℕ} (α : Fin N → ℝ) (e : Equiv.Perm (Fin N)) :
    terminal (α ∘ e)=terminal α := by
  exact Equiv.prod_comp e (fun s => (1-C (α s)*X))

/-- A finite product of affine root steps has degree at most its horizon. -/
theorem terminal_natDegree_le {N : ℕ} (α : Fin N → ℝ) : (terminal α).natDegree≤N := by
  calc
    _ ≤ ∑ s : Fin N, (1-C (α s)*X).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _s : Fin N, (1:ℕ) := by
      apply Finset.sum_le_sum
      intro s _
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · exact (natDegree_mul_le.trans (by simp))
    _ = N := by simp

/-- The zero-Hessian normalization of any literal root-step product is one. -/
@[simp] theorem terminal_zero {N : ℕ} (α : Fin N → ℝ) : (terminal α).eval 0=1 := by
  simp [terminal, eval_prod]

/-- The explicit reciprocal roots produce exactly the prescribed Chebyshev terminal. -/
theorem terminal_steps_eq (I : chebyshev1.SpectralInterval) (N : ℕ)
    (e : Equiv.Perm (Fin N)) : terminal (steps I N e)=I.residual N := by
  let points : Option (Fin N) → ℝ := fun t => match t with
    | none => 0
    | some s => node I N s
  have hp : Function.Injective points := by
    intro x y hxy
    cases x with
    | none => cases y with
      | none => rfl
      | some y =>
        have hy := I.mu_pos.trans (node_mem I N y).1
        change 0=node I N y at hxy
        linarith
    | some x => cases y with
      | none =>
        have hx := I.mu_pos.trans (node_mem I N x).1
        change node I N x=0 at hxy
        linarith
      | some y => exact congrArg some ((node_strictMono I N).injective hxy)
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hp
  · intro t
    cases t with
    | none =>
      change (terminal (steps I N e)).eval 0=(I.residual N).eval 0
      rw [terminal_zero, GradedFamily.residual_zero]
    | some s =>
      change (terminal (steps I N e)).eval (node I N s)=(I.residual N).eval (node I N s)
      rw [residual_node, terminal, eval_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ (e.symm s))
      simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, steps, Equiv.apply_symm_apply]
      rw [one_div_mul_cancel (ne_of_gt (I.mu_pos.trans (node_mem I N s).1)), sub_self]
  · rw [Fintype.card_option, Fintype.card_fin, I.residual_natDegree]
    exact Nat.lt_succ_of_le (max_le (terminal_natDegree_le _) le_rfl)

end
end bezout.Channel.Roots
