import polyak.FareyPlateau.Fan.Geometry

/-! Both signed Farey families give the two exact phase lattices. The lag
index is an arbitrary integer; no cutoff is used. -/
noncomputable section
namespace polyak.FareyPlateau.Fan.Data
open scoped BigOperators
variable (P : Fan.Data)

theorem sign_sq : P.sign^2=1 := by
  rcases P.sign_unit with h|h <;> rw [h] <;> norm_num

theorem grid_origin (n l : ℤ) :
    (n:ℝ)*P.near-(l:ℝ)*(2*Real.pi)=
      ((P.sign*(P.L*l-n*P.J):ℤ):ℝ)*P.k*P.delta := by
  have hk : (P.k:ℝ)≠0 := by exact_mod_cast (show P.k≠0 by have := P.period_ge; omega)
  have hL : (P.L:ℝ)≠0 := by exact_mod_cast (show P.L≠0 by have := P.period_ge; have := P.order_gt; omega)
  unfold near delta
  rcases P.sign_unit with h|h <;> rw [h] <;> push_cast <;> field_simp <;> ring

theorem sign_order_class (b : ℤ) (hb : b*P.j≡1 [ZMOD P.k]) :
    P.sign*P.L≡b [ZMOD P.k] := by
  have hd : P.k∣1-b*P.j := hb.dvd
  obtain ⟨v,hv⟩ := hd
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-P.sign*(v*P.L+b*P.J),?_⟩
  linear_combination -P.sign*P.L*hv + P.sign*b*P.incidence - b*P.sign_sq

theorem grid_edge (b n₁ n l : ℤ) (hb : b*P.j≡1 [ZMOD P.k])
    (hn : n₁%P.k=b%P.k) :
    ∃m : ℤ,(n:ℝ)*P.near-(l:ℝ)*(2*Real.pi)=
      2*Real.pi/P.k+((n₁:ℝ)+(m:ℝ)*P.k)*P.delta := by
  let r := P.sign*(P.L*l-n*P.J)
  let y := P.sign*P.L+P.k*r
  have hy : y≡n₁ [ZMOD P.k] := by
    change (P.sign*P.L+P.k*r)%P.k=n₁%P.k
    rw [Int.add_emod,Int.mul_emod_right,add_zero,Int.emod_emod]
    exact (P.sign_order_class b hb).trans (show b≡n₁ [ZMOD P.k] from hn.symm)
  obtain ⟨m,hm⟩ := hy.symm.dvd
  refine ⟨m,?_⟩
  have hmr : (y:ℝ)=(n₁:ℝ)+(m:ℝ)*P.k := by
    have hh : y=n₁+m*P.k := by linear_combination hm
    exact_mod_cast hh
  rw [←hmr,P.grid_origin]
  have hk : (P.k:ℝ)≠0 := by exact_mod_cast (show P.k≠0 by have := P.period_ge; omega)
  have hL : (P.L:ℝ)≠0 := by exact_mod_cast (show P.L≠0 by have := P.period_ge; have := P.order_gt; omega)
  change (r:ℝ)*P.k*P.delta=2*Real.pi/P.k+(y:ℝ)*P.delta
  unfold y delta
  rcases P.sign_unit with h|h <;> rw [h] <;> push_cast <;> field_simp <;> ring

theorem grid_lattices (b n₁ n l : ℤ) (hb : b*P.j≡1 [ZMOD P.k])
    (hn : n₁%P.k=b%P.k) :
    (∃r : ℤ,(n:ℝ)*P.near-(l:ℝ)*(2*Real.pi)=(r:ℝ)*P.k*P.delta) ∧
    (∃m : ℤ,(n:ℝ)*P.near-(l:ℝ)*(2*Real.pi)=
      2*Real.pi/P.k+((n₁:ℝ)+(m:ℝ)*P.k)*P.delta) :=
  ⟨⟨_,P.grid_origin n l⟩,P.grid_edge b n₁ n l hb hn⟩

end polyak.FareyPlateau.Fan.Data
