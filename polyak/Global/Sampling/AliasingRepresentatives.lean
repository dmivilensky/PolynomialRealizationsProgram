import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Balanced representatives of every nonzero signed residue, and the
uniform separation of nonprincipal aliases. -/
noncomputable section
namespace polyak.Global.Sampling

 theorem balanced_representative {L : ℕ} (hL : 0<L) (r : ℤ) :
    ∃n : ℤ,n%(L:ℤ)=r%(L:ℤ) ∧ 2*|n|≤(L:ℤ) ∧
      ((r%(L:ℤ)=0 ↔ n=0)) := by
  let s:=r%(L:ℤ)
  have hs : 0≤s:=Int.emod_nonneg r (by exact_mod_cast hL.ne')
  have hsL : s<(L:ℤ):=Int.emod_lt_of_pos r (by exact_mod_cast hL)
  by_cases hhalf : 2*s≤(L:ℤ)
  · refine ⟨s,by dsimp [s]; rw [Int.emod_emod],?_,?_⟩
    · rwa [abs_of_nonneg hs]
    · rfl
  · refine ⟨s-L,?_,?_,?_⟩
    · dsimp [s]
      simp only [Int.sub_emod,Int.emod_self,sub_zero,Int.emod_emod]
    · rw [abs_of_neg (by omega : s-(L:ℤ)<0)]
      omega
    · constructor
      · intro hz
        change s=0 at hz
        omega
      · intro hz
        omega

 theorem alias_separation {L : ℕ} (hL : 0<L) {n m : ℤ}
    (hn : 2*|n|≤(L:ℤ)) (hm : m≠0) :
    (L:ℝ)*|(m:ℝ)|/2≤|((m*(L:ℤ)-n:ℤ):ℝ)| := by
  have hm1 : (1:ℤ)≤|m|:=Int.one_le_abs hm
  have htri : |m*(L:ℤ)|≤|m*(L:ℤ)-n|+|n|:=by
    simpa only [sub_add_cancel] using abs_add_le (m*(L:ℤ)-n) n
  rw [abs_mul,abs_of_nonneg (by exact_mod_cast hL.le : (0:ℤ)≤L)] at htri
  have hnr : 2*|(n:ℝ)|≤L:=by exact_mod_cast hn
  have hmr : (1:ℝ)≤|(m:ℝ)|:=by exact_mod_cast hm1
  have htr : |(m:ℝ)| *L≤|((m*(L:ℤ)-n:ℤ):ℝ)|+|(n:ℝ)|:=by exact_mod_cast htri
  have hLr : (0:ℝ)≤L:=by positivity
  nlinarith [mul_le_mul_of_nonneg_right hmr hLr]

end polyak.Global.Sampling
