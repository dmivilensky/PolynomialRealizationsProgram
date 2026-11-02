import krylov.Tensor.QuarticBanach

/-!
Article: main_krylov, thm:Fexact, actual quartic diagonal-to-mixed norm identity.
Use: obtain the true compact tensor maximum, maximize its vector-sum norm,
and apply the proved pair-normalization argument in all three required pair
positions. Source: Banach (1938), compactness and symmetric polarization.
-/

namespace krylov.Tensor
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Compactness gives a true maximum of the actual quartic on four unit spheres.
Article: main_krylov, thm:Fexact, Banach's quartic theorem. -/
theorem exists_quartic_mixed_max [Nontrivial E] (Q : SymmetricQuartic E) :
    ∃ x y z w : E, ‖x‖=1 ∧ ‖y‖=1 ∧ ‖z‖=1 ∧ ‖w‖=1 ∧
      ∀ u v a b : E, ‖u‖=1 → ‖v‖=1 → ‖a‖=1 → ‖b‖=1 →
        |Q.form u v a b|≤|Q.form x y z w| := by
  let S := Metric.sphere (0:E) 1
  let K : Set ((E×E)×(E×E)) := (S ×ˢ S) ×ˢ (S ×ˢ S)
  have hS : IsCompact S := isCompact_sphere (0:E) 1
  have hK : IsCompact K := (hS.prod hS).prod (hS.prod hS)
  obtain ⟨e,he⟩ := exists_norm_eq E (show (0:ℝ)≤1 by norm_num)
  have hne : K.Nonempty := by
    refine ⟨((e,e),(e,e)),?_⟩
    simpa [K,S,Metric.mem_sphere,dist_zero_right] using And.intro (And.intro he he) (And.intro he he)
  obtain ⟨p,hp,hmax⟩ := hK.exists_isMaxOn hne (continuous_quartic_tuple Q).continuousOn
  have hp' : (‖p.1.1‖=1 ∧ ‖p.1.2‖=1) ∧ (‖p.2.1‖=1 ∧ ‖p.2.2‖=1) := by
    simpa [K,S,Metric.mem_sphere,dist_zero_right] using hp
  refine ⟨p.1.1,p.1.2,p.2.1,p.2.2,hp'.1.1,hp'.1.2,hp'.2.1,hp'.2.2,?_⟩
  intro u v a b hu hv ha hb
  exact hmax (a := ((u,v),(a,b))) (by
    simpa [K,S,Metric.mem_sphere,dist_zero_right] using And.intro (And.intro hu hv) (And.intro ha hb))

/-- The actual mixed quartic maximum has a genuine diagonal unit attainer.
Article: main_krylov, thm:Fexact, Banach's quartic theorem.
Proof: on the compact set of genuine maximum tuples maximize the vector-sum
norm. Apply the pair-normalization theorem to three pair permutations;
tensor symmetry preserves the objective, and addition preserves the sum. -/
theorem exists_quartic_diagonal_max (Q : SymmetricQuartic E) (M : ℝ)
    (hbound : ∀ u v z w : E, ‖u‖=1 → ‖v‖=1 → ‖z‖=1 → ‖w‖=1 → |Q.form u v z w|≤M)
    (hex : ∃ x y z w : E, ‖x‖=1 ∧ ‖y‖=1 ∧ ‖z‖=1 ∧ ‖w‖=1 ∧ |Q.form x y z w|=M) :
    ∃ x : E, ‖x‖=1 ∧ |Q.form x x x x|=M := by
  let S := Metric.sphere (0:E) 1
  let K : Set ((E×E)×(E×E)) := (S ×ˢ S) ×ˢ (S ×ˢ S)
  let A : Set ((E×E)×(E×E)) := K ∩ {p | |Q.form p.1.1 p.1.2 p.2.1 p.2.2|=M}
  have hS : IsCompact S := isCompact_sphere (0:E) 1
  have hK : IsCompact K := (hS.prod hS).prod (hS.prod hS)
  have hA : IsCompact A := hK.inter_right (isClosed_eq (continuous_quartic_tuple Q) continuous_const)
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hval⟩ := hex
  have hne : A.Nonempty := by
    refine ⟨((a,b),(c,d)),?_,hval⟩
    simpa [K,S,Metric.mem_sphere,dist_zero_right] using And.intro (And.intro ha hb) (And.intro hc hd)
  have hsum : Continuous (fun p : (E×E)×(E×E) => ‖p.1.1+p.1.2+p.2.1+p.2.2‖) :=
    (((continuous_fst.fst.add continuous_fst.snd).add continuous_snd.fst).add continuous_snd.snd).norm
  obtain ⟨p,hp,hmax⟩ := hA.exists_isMaxOn hne hsum.continuousOn
  let x := p.1.1
  let y := p.1.2
  let z := p.2.1
  let w := p.2.2
  have hp' : (‖x‖=1 ∧ ‖y‖=1) ∧ (‖z‖=1 ∧ ‖w‖=1) := by
    simpa [K,S,Metric.mem_sphere,dist_zero_right,x,y,z,w] using hp.1
  obtain ⟨⟨hx,hy⟩,hz,hw⟩ := hp'
  have hQ : |Q.form x y z w|=M := hp.2
  have htuple : ∀ u v z' w' : E, ‖u‖=1 → ‖v‖=1 → ‖z'‖=1 → ‖w'‖=1 →
      |Q.form u v z' w'|=M → ‖u+v+z'+w'‖≤‖x+y+z+w‖ := by
    intro u v z' w' hu hv hz' hw' hval'
    exact hmax (a := ((u,v),(z',w'))) ⟨by
      simpa [K,S,Metric.mem_sphere,dist_zero_right] using And.intro (And.intro hu hv) (And.intro hz' hw'),hval'⟩
  have hxy := quartic_max_sum_pair_eq Q M hbound x y z w hx hy hz hw hQ htuple
  have hxz : x=z := by
    apply quartic_max_sum_pair_eq Q M hbound x z y w hx hz hy hw
    · rw [← Q.swap₂ x y z w]
      exact hQ
    · intro u v z' w' hu hv hz' hw' hval'
      have h := htuple u v z' w' hu hv hz' hw' hval'
      rwa [show x+y+z+w=x+z+y+w by abel] at h
  have hxw : x=w := by
    apply quartic_max_sum_pair_eq Q M hbound x w y z hx hw hy hz
    · rw [Q.swap₂ x w y z,Q.swap₃ x y w z]
      exact hQ
    · intro u v z' w' hu hv hz' hw' hval'
      have h := htuple u v z' w' hu hv hz' hw' hval'
      rwa [show x+y+z+w=x+w+y+z by abel] at h
  exact ⟨x,hx,by simpa only [← hxy,← hxz,← hxw] using hQ⟩

/-- Banach's full diagonal-to-mixed bound for a genuine symmetric quartic on
unit vectors in a finite dimensional real Hilbert space.
Article: main_krylov, thm:Fexact, the diagonal-only M4 hypothesis. -/
theorem quartic_diagonal_bound_mixed (Q : SymmetricQuartic E) (C : ℝ)
    (hdiag : ∀ u : E, ‖u‖=1 → |Q.form u u u u|≤C)
    (x y z w : E) (hx : ‖x‖=1) (hy : ‖y‖=1) (hz : ‖z‖=1) (hw : ‖w‖=1) :
    |Q.form x y z w|≤C := by
  have : Nontrivial E := nontrivial_of_ne x 0 (by intro h;simp [h] at hx)
  obtain ⟨a,b,c,d,ha,hb,hc,hd,hmax⟩ := exists_quartic_mixed_max Q
  obtain ⟨u,hu,huM⟩ := exists_quartic_diagonal_max Q |Q.form a b c d| hmax ⟨a,b,c,d,ha,hb,hc,hd,rfl⟩
  have hC : |Q.form a b c d|≤C := huM ▸ hdiag u hu
  exact (hmax x y z w hx hy hz hw).trans hC

/-- The exact product-of-norms quartic bound, including all zero-vector cases.
Article: main_krylov, thm:Fexact, Banach's fourth-degree norm identity. -/
theorem quartic_diagonal_bound (Q : SymmetricQuartic E) (C : ℝ)
    (hdiag : ∀ u : E, ‖u‖=1 → |Q.form u u u u|≤C)
    (x y z w : E) : |Q.form x y z w|≤C*‖x‖*‖y‖*‖z‖*‖w‖ := by
  by_cases hx : x=0
  · rw [hx,quartic_zero_first]
    simp
  by_cases hy : y=0
  · simp [hy]
  by_cases hz : z=0
  · simp [hz]
  by_cases hw : w=0
  · simp [hw]
  have hb := quartic_diagonal_bound_mixed Q C hdiag
    (NormedSpace.normalize x) (NormedSpace.normalize y) (NormedSpace.normalize z) (NormedSpace.normalize w)
    (NormedSpace.norm_normalize hx) (NormedSpace.norm_normalize hy)
    (NormedSpace.norm_normalize hz) (NormedSpace.norm_normalize hw)
  have he : Q.form x y z w=(‖x‖*‖y‖*‖z‖*‖w‖)*
      Q.form (NormedSpace.normalize x) (NormedSpace.normalize y) (NormedSpace.normalize z) (NormedSpace.normalize w) := by
    conv_lhs => rw [← NormedSpace.norm_smul_normalize x,← NormedSpace.norm_smul_normalize y,
      ← NormedSpace.norm_smul_normalize z,← NormedSpace.norm_smul_normalize w]
    simp only [map_smul,smul_apply,smul_eq_mul]
    ring
  rw [he,abs_mul,abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hb (by positivity : 0≤‖x‖*‖y‖*‖z‖*‖w‖)]

end
end krylov.Tensor
