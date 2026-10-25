import polyak.FareyPlateau.Edge.Singleton
import polyak.ModeLocking.Periods.Least

/-! A reduced singleton support forces its exact denominator as the nominal
regular period. This removes an arbitrary-period hypothesis in the plateau converse. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels ModeLocking Set

theorem rational_atom_period {j k L : ℕ} (hk : 0<k) (hjk : 2*j≤k)
    (b : ℤ) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (hgrid : Edge.atom j k hk hjk∈periodicGrid L) : k∣L := by
  obtain ⟨_,m,hm⟩ := hgrid
  change (L:ℝ)*(2*Real.pi*j/k)=(m:ℝ)*(2*Real.pi) at hm
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have he : (L:ℤ)*(j:ℤ)=m*(k:ℤ) := by
    have heq := congrArg (fun z:ℝ=>z*(k:ℝ)) hm
    field_simp at heq
    have hh : (L:ℝ)*j=(m:ℝ)*k := by nlinarith [Real.pi_pos]
    exact_mod_cast hh
  obtain ⟨z,hz⟩ := hb.symm.dvd
  have hdiv : (k:ℤ)∣(L:ℤ) := by
    refine ⟨b*m-(L:ℤ)*z,?_⟩
    linear_combination b*he - (L:ℤ)*hz
  exact_mod_cast hdiv

theorem singleton_regular_period {q : Tuning} {s : ℝ} {L j k : ℕ}
    (D : RegularData q s L) (hk : 0<k) (hj : 1≤j) (hjk : 2*j≤k)
    (b : ℤ) (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)])
    (hS : Set.range D.atoms={Edge.atom j k hk hjk}) : L=k := by
  have hatom (i : Fin D.d) : D.atoms i=Edge.atom j k hk hjk := by
    have hi : D.atoms i∈Set.range D.atoms := ⟨i,rfl⟩
    simpa only [hS,mem_singleton_iff] using hi
  have hd : L∣k := (D.support_period_iff_dvd k).mp (fun i=>by
    rw [hatom i]
    exact Edge.atom_grid hj hk hjk)
  have hd' : k∣L := rational_atom_period hk hjk b hb (by
    simpa only [hatom] using D.atoms_grid ⟨0,D.d_pos⟩)
  exact Nat.dvd_antisymm hd hd'

end polyak.FareyPlateau
