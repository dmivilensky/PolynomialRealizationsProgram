import polyak.Farey.Records.Selection

/-! Both Farey spines, at every permitted anchor depth. The second spine
uses the normalized representative k-K of the signed multiplier -K. -/
namespace polyak.Farey

theorem first_spine_selection {K p t : ℤ} {ac : ℝ} (hK : 2≤K) (hp : 2≤p)
    (ht : 2≤t) (htp : t≤p) (hac : (p-1:ℤ) < ac) :
    RecordSelection (p*K+1) t (K+1) ac ↔ ac < (K+1:ℤ) := by
  have hkp : K+1 < p*K+1 := by nlinarith
  have hr1 : residue (p*K+1) (K+1) 1=K+1 :=
    residue_eq_of_lattice (by omega) hkp (q:=0) (by ring)
  constructor
  · intro hs
    have hh := hs 1 (by omega) (by omega)
    rwa [hr1] at hh
  · intro hs
    have hpK : p≤K+1 := by
      have hR : (p:ℝ)-1 < (K:ℝ)+1 := by exact_mod_cast hac.trans hs
      have hR' : (p:ℝ) < (K:ℝ)+2 := by linarith
      have hi : p < K+2 := by exact_mod_cast hR'
      omega
    intro r hr hrt
    have hrp : r≤p-1 := by omega
    have hlow : K+1≤r*(K+1) := by nlinarith
    have hhigh : r*(K+1) < p*K+1 := by
      have hm := mul_le_mul_of_nonneg_right hrp (by omega : 0≤K+1)
      nlinarith
    have hres : residue (p*K+1) (K+1) r=r*(K+1) :=
      residue_eq_of_lattice (by nlinarith) hhigh (q:=0) (by ring)
    rw [hres]
    exact hs.trans_le (by exact_mod_cast hlow)

theorem first_spine_forces_depth {K p t : ℤ} {ac : ℝ} (hK : 2≤K) (hp : 2≤p)
    (ht : 2≤t) (htp : t≤p) (hac : (p-1:ℤ) < ac)
    (hs : RecordSelection (p*K+1) t (K+1) ac) : p≤K+1 := by
  have hh := (first_spine_selection hK hp ht htp hac).mp hs
  have hhR : (p:ℝ)-1 < (K:ℝ)+1 := by exact_mod_cast hac.trans hh
  have hR : (p:ℝ) < (K:ℝ)+2 := by linarith
  have hi : p < K+2 := by exact_mod_cast hR
  omega

theorem second_spine_residue {K l r : ℤ} (hK : 2≤K) (hl : 1≤l)
    (hr : 1≤r) (hrl : r≤l) :
    residue (K+l*(K+1)) (K+l*(K+1)-K) r=K+l*(K+1)-r*K := by
  have hrK : 0 < r*K := mul_pos (by omega) (by omega)
  have htop : r*K < K+l*(K+1) := by
    have hm := mul_le_mul_of_nonneg_right hrl (by omega : 0≤K)
    nlinarith
  apply residue_eq_of_lattice (by omega) (by omega) (q:=r-1)
  ring

theorem second_spine_selection {K l t : ℤ} {ac : ℝ} (hK : 2≤K) (hl : 1≤l)
    (ht : 2≤t) (htl : t≤l+1) :
    RecordSelection (K+l*(K+1)) t (K+l*(K+1)-K) ac ↔
      ac < (K+l*(K+1)-(t-1)*K:ℤ) := by
  constructor
  · intro hs
    have hh := hs (t-1) (by omega) (by omega)
    rwa [second_spine_residue hK hl (by omega) (by omega)] at hh
  · intro hs r hr hrt
    rw [second_spine_residue hK hl hr (by omega)]
    have hm := mul_le_mul_of_nonneg_right (show r≤t-1 by omega) (show 0≤K by omega)
    exact hs.trans_le (by exact_mod_cast (show K+l*(K+1)-(t-1)*K≤K+l*(K+1)-r*K by omega))

theorem second_spine_full_selection {K l : ℤ} {ac : ℝ} (hK : 2≤K) (hl : 1≤l) :
    RecordSelection (K+l*(K+1)) (l+1) (K+l*(K+1)-K) ac ↔ ac < (K+l:ℤ) := by
  rw [second_spine_selection hK hl (by omega) le_rfl]
  have he : K+l*(K+1)-((l+1)-1)*K=K+l := by ring
  rw [he]

theorem first_spine_auxiliary (K p : ℤ) : p*(K+1)=1*(p*K+1)+(p-1) := by ring

theorem second_spine_auxiliary (K l : ℤ) :
    (l+1)*(K+l*(K+1)-K)=l*(K+l*(K+1))+l := by ring

end polyak.Farey
