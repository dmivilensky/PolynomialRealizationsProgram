import chebyshev1.Stochastic.GossipGraph
import Mathlib.Logic.Relation

/-! Positive weighted connected graphs have precisely the constant vectors in their kernel. -/
namespace chebyshev1.Background
noncomputable section
open Matrix
open scoped BigOperators
variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e]

/-- The unoriented adjacency relation of the supplied edge list. -/
def EdgeAdjacent (a b : e → d) (i j : d) : Prop :=
  ∃ k, (a k = i ∧ b k = j) ∨ (b k = i ∧ a k = j)

/-- Ordinary path connectivity, allowing each listed edge in either orientation. -/
def EdgesConnected (a b : e → d) : Prop :=
  ∀ i j, Relation.ReflTransGen (EdgeAdjacent a b) i j

def weightedLaplacian (w : e → ℝ) (a b : e → d) : Matrix d d ℝ :=
  Stochastic.edgeLaplacian w (fun k => Stochastic.incidence (a k) (b k))

omit [Fintype d] in
theorem weightedLaplacian_isHermitian (w : e → ℝ) (a b : e → d) :
    (weightedLaplacian w a b).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [weightedLaplacian, Stochastic.edgeLaplacian, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec, Matrix.of_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem weightedLaplacian_energy (w : e → ℝ) (a b : e → d) (v : d → ℝ) :
    dotProduct v ((weightedLaplacian w a b).mulVec v) =
      ∑ k, w k * (v (a k) - v (b k))^2 := by
  rw [weightedLaplacian, Stochastic.edgeLaplacian_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [Stochastic.incidence, dotProduct_smul, dotProduct_sub, sub_dotProduct,
    single_dotProduct, dotProduct_single, pow_two, mul_comm, mul_left_comm]

theorem weightedLaplacian_energy_nonneg (w : e → ℝ) (hw : ∀ k, 0 ≤ w k)
    (a b : e → d) (v : d → ℝ) :
    0 ≤ dotProduct v ((weightedLaplacian w a b).mulVec v) := by
  rw [weightedLaplacian_energy]
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hw k) (sq_nonneg _))

theorem weightedLaplacian_energy_zero_iff (w : e → ℝ) (hw : ∀ k, 0 < w k)
    (a b : e → d) (v : d → ℝ) :
    dotProduct v ((weightedLaplacian w a b).mulVec v) = 0 ↔
      ∀ k, v (a k) = v (b k) := by
  rw [weightedLaplacian_energy]
  constructor
  · intro hz k
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => mul_nonneg (hw k).le (sq_nonneg _))).mp hz k (Finset.mem_univ k)
    have hs : (v (a k) - v (b k))^2 = 0 := (mul_eq_zero.mp ht).resolve_left (hw k).ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro hv
    simp [hv]

omit [Fintype d] [DecidableEq d] [Fintype e] in
theorem constant_on_connected_edges (a b : e → d) (hc : EdgesConnected a b)
    (v : d → ℝ) (hv : ∀ k, v (a k) = v (b k)) (i j : d) : v i = v j := by
  have hpath := hc i j
  induction hpath with
  | refl => rfl
  | @tail j k hpath hadj ih =>
    apply ih.trans
    obtain ⟨r, hr | hr⟩ := hadj
    · simpa only [hr.1, hr.2] using hv r
    · simpa only [hr.1, hr.2] using (hv r).symm

theorem weightedLaplacian_mulVec_const (w : e → ℝ) (a b : e → d) (c : ℝ) :
    (weightedLaplacian w a b).mulVec (fun _ => c) = 0 := by
  rw [weightedLaplacian, Stochastic.edgeLaplacian_mulVec]
  simp [Stochastic.incidence, sub_dotProduct]

/-- Connectivity and positive weights give the exact one-dimensional nullspace. -/
theorem weightedLaplacian_kernel_iff [Nonempty d] (w : e → ℝ) (hw : ∀ k, 0 < w k)
    (a b : e → d) (hc : EdgesConnected a b) (v : d → ℝ) :
    (weightedLaplacian w a b).mulVec v = 0 ↔ ∃ c : ℝ, v = fun _ => c := by
  constructor
  · intro hz
    have he : dotProduct v ((weightedLaplacian w a b).mulVec v) = 0 := by rw [hz]; simp
    have hv := (weightedLaplacian_energy_zero_iff w hw a b v).mp he
    let i : d := Classical.choice inferInstance
    refine ⟨v i, ?_⟩
    funext j
    exact constant_on_connected_edges a b hc v hv j i
  · rintro ⟨c, rfl⟩
    exact weightedLaplacian_mulVec_const w a b c

/-- The graph Laplacian is strictly positive on the mean-zero error space. -/
theorem weightedLaplacian_meanZero_pos [Nonempty d] (w : e → ℝ) (hw : ∀ k, 0 < w k)
    (a b : e → d) (hc : EdgesConnected a b) (v : d → ℝ)
    (hmean : ∑ i, v i = 0) (hv : v ≠ 0) :
    0 < dotProduct v ((weightedLaplacian w a b).mulVec v) := by
  have hn := weightedLaplacian_energy_nonneg w (fun k => (hw k).le) a b v
  apply lt_of_le_of_ne hn
  intro hz
  have hedge := (weightedLaplacian_energy_zero_iff w hw a b v).mp hz.symm
  let i : d := Classical.choice inferInstance
  have he : v = fun _ => v i := by
    funext j
    exact constant_on_connected_edges a b hc v hedge j i
  have hi : v i = 0 := by
    rw [he] at hmean
    have hcard : (Fintype.card d : ℝ) * v i = 0 := by simpa using hmean
    exact (mul_eq_zero.mp hcard).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  apply hv
  rw [he, hi]
  rfl

/-- Every nonzero real graph eigenvalue is positive, with no gap assumed. -/
theorem weightedLaplacian_nonzero_eigenvalue_pos [Nonempty d]
    (w : e → ℝ) (hw : ∀ k, 0 < w k) (a b : e → d) (hc : EdgesConnected a b)
    (lam : ℝ) (hlam : lam ≠ 0) (v : d → ℝ) (hv : v ≠ 0)
    (heigen : (weightedLaplacian w a b).mulVec v = lam • v) : 0 < lam := by
  have hm : ∑ i, v i = 0 := by
    have hh := Stochastic.edgeLaplacian_mulVec_sum w
      (fun k => Stochastic.incidence (a k) (b k))
      (fun k => Stochastic.incidence_sum (a k) (b k)) v
    change ∑ i, (weightedLaplacian w a b).mulVec v i = 0 at hh
    rw [heigen] at hh
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at hh
    exact (mul_eq_zero.mp hh).resolve_left hlam
  have hp := weightedLaplacian_meanZero_pos w hw a b hc v hm hv
  rw [heigen, dotProduct_smul, smul_eq_mul] at hp
  have hnorm : 0 ≤ dotProduct v v := by
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
  by_contra hh
  have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) hnorm
  linarith

/-- Finitely many positive active eigenvalues admit a positive common lower bound. -/
theorem weightedLaplacian_spectral_gap [Nonempty d]
    (w : e → ℝ) (hw : ∀ k, 0 < w k) (a b : e → d) (hc : EdgesConnected a b) :
    let hH := weightedLaplacian_isHermitian w a b
    ∃ mu : ℝ, 0 < mu ∧ ∀ j, hH.eigenvalues j ≠ 0 → mu ≤ hH.eigenvalues j := by
  dsimp only
  let hH := weightedLaplacian_isHermitian w a b
  have hp (j : d) (hj : hH.eigenvalues j ≠ 0) : 0 < hH.eigenvalues j := by
    apply weightedLaplacian_nonzero_eigenvalue_pos w hw a b hc _ hj
      (fun i => hH.eigenvectorBasis j i) ?_ (hH.mulVec_eigenvectorBasis j)
    intro hz
    apply hH.eigenvectorBasis.orthonormal.ne_zero j
    exact PiLp.ext (fun i => congrFun hz i)
  have hf (s : Finset d) : ∃ mu : ℝ, 0 < mu ∧
      ∀ j ∈ s, hH.eigenvalues j ≠ 0 → mu ≤ hH.eigenvalues j := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert j s hj ih =>
      obtain ⟨mu, hmu, hs⟩ := ih
      by_cases hz : hH.eigenvalues j = 0
      · refine ⟨mu, hmu, ?_⟩
        intro k hk hk0
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact (hk0 hz).elim
        · exact hs k hk hk0
      · refine ⟨min mu (hH.eigenvalues j), lt_min hmu (hp j hz), ?_⟩
        intro k hk hk0
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hs k hk hk0)
  obtain ⟨mu, hmu, hm⟩ := hf Finset.univ
  exact ⟨mu, hmu, fun j hj => hm j (Finset.mem_univ j) hj⟩

end
end chebyshev1.Background
