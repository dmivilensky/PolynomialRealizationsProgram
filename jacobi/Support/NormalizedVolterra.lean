import jacobi.Support.VolterraKernelBounds

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Dividing the actual finite wave by its positive top-node solution gives
an exact nested Volterra equation. Its two-index kernel is uniformly
bounded on the complete half triangle, including the corner at zero.
This is the nonsingular form used to pass to the continuum edge limit.
Use: naturalWave_normalizedVolterra gives the exact finite equation, and normalizedKernel_bound supplies its endpoint-independent mesh majorant.
-/
namespace jacobi.Support
noncomputable section
open Real Filter Finset jacobi.Reference jacobi.Finite
open scoped Topology

/-- The actual finite reduction-of-order kernel after ground normalization and before summing the intermediate index.
Use: naturalWave_normalizedVolterra gives the exact finite equation, and normalizedKernel_bound supplies its endpoint-independent mesh majorant.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
-/
def normalizedKernel (a b : ℝ) (ha : -1<a) (hb : -1<b) (n l j : ℕ) : ℝ :=
  (topValue a b ha hb n j)^2 /
    (sqrt ((naturalChain a b ha hb (n+1)).data.aSq (l+1))*
      topValue a b ha hb n l*topValue a b ha hb n (l+1))

/-- The actual complex finite wave satisfies its exact ground-normalized nested Volterra equation.
Use: the complex edge limit compares these actual finite nested sums with groundVolterra, whose genuine reference solution has already been identified.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: divide the proved original Green equation by its positive original top-node value. Interchange its finite triangular sums and replace each inner wave by its own ground value times its actual normalized quotient. -/
theorem naturalWave_normalizedVolterra (a b : ℝ) (ha : -1<a) (hb : -1<b)
    (n m : ℕ) (hm : m≤n) (y : ℂ) :
    naturalWave a b ha hb n m y/(topValue a b ha hb n m:ℂ)=1+
      (y-(cos (gamma a*step a b (n+1)):ℝ))*
        ∑l∈range m,∑j∈range (l+1),(normalizedKernel a b ha hb n l j:ℂ)*
          (naturalWave a b ha hb n j y/(topValue a b ha hb n j:ℂ)) := by
  -- Every division below uses the same genuinely positive finite ground solution.
  let u : ℕ→ℂ := fun j => (topValue a b ha hb n j:ℂ)
  let v : ℕ→ℂ := fun j => naturalWave a b ha hb n j y
  let f : ℕ→ℂ := fun l =>
    ((sqrt ((naturalChain a b ha hb (n+1)).data.aSq (l+1)):ℂ)*u l*u (l+1))⁻¹
  have hu (j : ℕ) (hj : j≤n) : u j≠0 :=
    Complex.ofReal_ne_zero.mpr (naturalPolynomial_top_pos ha hb hj).ne'
  have hs : (∑j∈range m,(volterraKernel a b ha hb n m j:ℂ)*v j)/u m=
      ∑l∈range m,∑j∈range (l+1),(normalizedKernel a b ha hb n l j:ℂ)*(v j/u j) := by
    calc
      _ = ∑j∈range m,(u j*v j)*∑l∈Ico j m,f l := by
        rw [sum_div]
        apply sum_congr rfl
        intro j _
        simp only [volterraKernel,Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_inv]
        change (u m*u j*∑l∈Ico j m,f l)*v j/u m=_
        field_simp [hu m hm]
      _ = ∑l∈range m,f l*∑j∈range (l+1),u j*v j :=
        (triangular_sum_swap f (fun j => u j*v j) m).symm
      _ = _ := by
        apply sum_congr rfl
        intro l hl
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        have hjn : j≤n := by have := mem_range.mp hl; have := mem_range.mp hj; omega
        simp only [normalizedKernel,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_mul]
        change f l*(u j*v j)=u j^2/
          ((sqrt ((naturalChain a b ha hb (n+1)).data.aSq (l+1)):ℂ)*u l*u (l+1))*(v j/u j)
        dsimp [f]
        field_simp [hu j hjn]
  rw [naturalWave_volterra a b ha hb n m hm y,add_div,div_self (hu m hm),mul_div_assoc]
  change 1+_ * ((∑j∈range m,(volterraKernel a b ha hb n m j:ℂ)*v j)/u m)=_
  rw [hs]

/-- The genuine ground-normalized finite kernel has one uniform nonnegative constant bound on the full physical half triangle.
Use: the finite nested mesh sums admit dominated convergence through their original zero corner; complex edge stability uses the same bound without any singular-exponent case split.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the actual top-node values have uniform two-sided power growth, and every used coupling has a uniform positive lower bound. For j<=l the original increasing power at j is no larger than those at l and l+1. Comparing the numerator and denominator cancels that same positive power square. -/
theorem normalizedKernel_bound {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃B:ℝ,0<B ∧ ∀ᶠn:ℕ in atTop,∀l j:ℕ,2*l≤n→j≤l→
      0≤normalizedKernel a b ha hb n l j ∧ normalizedKernel a b ha hb n l j≤B := by
  -- The original singular endpoint disappears before taking a limit or introducing an integral.
  obtain ⟨c,C,hc,hC,hbounds⟩ := topValue_bounds ha hb
  obtain ⟨A,D,hA,hD,hcoeff⟩ := coefficient_bounds ha hb
  refine ⟨C^2/(A*c^2),by positivity,?_⟩
  filter_upwards [hbounds,(tendsto_add_atTop_nat 1).eventually hcoeff,eventually_ge_atTop (6:ℕ)] with n hn he hnlarge
  intro l j hl hj
  let w : ℕ→ℝ := fun k => ((k:ℝ)+1)^gamma a
  have hw (k:ℕ) : 0<w k := rpow_pos_of_pos (by positivity) _
  have hmono {r s:ℕ} (hrs:r≤s) : w r≤w s :=
    rpow_le_rpow (by positivity) (by exact_mod_cast Nat.add_le_add_right hrs 1) (parameter_pos ha hb).1.le
  have hjb := hn j (by omega)
  have hlb := hn l (by omega)
  have hlb' := hn (l+1) (by omega)
  have hju : 0≤topValue a b ha hb n j := (mul_pos hc (hw j)).le.trans hjb.1
  have hlu : c*w j≤topValue a b ha hb n l :=
    (mul_le_mul_of_nonneg_left (hmono hj) hc.le).trans hlb.1
  have hlu' : c*w j≤topValue a b ha hb n (l+1) :=
    (mul_le_mul_of_nonneg_left (hmono (by omega : j≤l+1)) hc.le).trans hlb'.1
  have hac := (he.2 (l+1) (by omega) (by omega)).1
  have hden : A*c^2*(w j)^2≤sqrt ((naturalChain a b ha hb (n+1)).data.aSq (l+1))*
      topValue a b ha hb n l*topValue a b ha hb n (l+1) := by
    convert mul_le_mul (mul_le_mul hac hlu (by positivity) (hA.le.trans hac)) hlu'
      (by positivity) (mul_nonneg (hA.le.trans hac) ((mul_pos hc (hw j)).le.trans hlu)) using 1
    ring
  have hdenpos : 0<A*c^2*(w j)^2 := by positivity
  refine ⟨div_nonneg (sq_nonneg _) (hdenpos.le.trans hden),?_⟩
  calc
    _ ≤ (C*w j)^2/(A*c^2*(w j)^2) :=
      div_le_div₀ (sq_nonneg _) ((sq_le_sq₀ hju (by positivity)).mpr hjb.2) hdenpos hden
    _ = _ := by field_simp [(hw j).ne']

end
end jacobi.Support
