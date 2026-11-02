import jacobi.Analysis.UniformMeshSquares

/-!
Article: jacobi, Theorem 2.1.
The exact finite mesh-integration theorem from chebyshev1 applies
unchanged to arrays indexed by the genuine matrix dimension N=n+1.
No initial zero-dimensional matrix or missing cell is introduced.
Use: the original finite Green diagonal yields exactly the energy limit E(J^*_N)/N^3=c_star(alpha) in Theorem 2.1.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology

/-- A genuine successor-dimension mesh with a uniform continuous
profile limit has its exact normalized squared-sum limit.
Use: the original finite Green diagonal yields exactly the energy
limit E(J^*_N)/N^3=c_star(alpha) in Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: pad the same actual array by zero outside its finite dimension.
The proved uniform mesh theorem applies to positive dimensions; its
cofinal successor subsequence is exactly the original finite sum. -/
theorem successor_mesh_square_integral (a:∀n:ℕ,Fin (n+1)→ℝ) (f:ℝ→ℝ) (hf:Continuous f)
    (ha:∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀i:Fin (n+1),
      |a n i-f ((i.val:ℝ)/((n:ℝ)+1))|<ε) :
    Tendsto (fun n:ℕ => (∑i:Fin (n+1),(a n i)^2)/((n:ℝ)+1)) atTop
      (𝓝 (∫t in (0:ℝ)..1,(f t)^2)) := by
  -- The array at dimension m uses precisely the original degree m-1.
  let b (m j:ℕ) : ℝ := if hj:j<m then a (m-1) ⟨j,by omega⟩ else 0
  have hb : ∀ε:ℝ,0<ε→∃N:ℕ,∀m≥N,∀j<m,|b m j-f ((j:ℝ)/(m:ℝ))|<ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := ha ε hε
    refine ⟨N+1,fun m hm j hj => ?_⟩
    have hm0 : 0<m := by omega
    have hdim : m-1+1=m := by omega
    have hh := hN (m-1) (by omega) ⟨j,by omega⟩
    simpa only [b,dite_eq_left hj,show ((m-1:ℕ):ℝ)+1=(m:ℝ) by exact_mod_cast hdim] using hh
  have hh := (uniform_mesh_square_integral b f hf hb).comp (tendsto_add_atTop_nat 1)
  apply hh.congr'
  exact Eventually.of_forall (fun n => by
    dsimp only [Function.comp_def]
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [Nat.cast_add,Nat.cast_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [b,i.isLt])

end
end jacobi.Analysis
