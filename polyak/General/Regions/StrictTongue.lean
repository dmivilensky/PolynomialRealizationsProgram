import polyak.General.Regions.SingleFeasible

/-! Article: Theorem A(ii), strict phase inequality implies rho>1.
The neighborhood controls finitely many residues, then covers all infinitely
many lags exactly by root-of-unity periodicity and cosh(nt)>=1. -/
namespace polyak.General.Regions
noncomputable section
open Filter Spectral
open scoped Topology

private theorem polygon_cosine_strict {k : ℕ} (hk : 3≤k) {θ : ℝ}
    (hθ : 0≤θ) (hθk : θ<Real.pi/k) {l : ℕ} (hl0 : 1≤l) (hl : l<k) :
    Real.cos (2*Real.pi*l/k-θ)<Real.cos θ := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hl1 : (1:ℝ)≤l := by exact_mod_cast hl0
  have hlk : (l:ℝ)≤k-1 := by
    have hh : (l:ℝ)+1≤k := by exact_mod_cast (show l+1≤k by omega)
    linarith
  have hm : 2*Real.pi*l/k=2*(Real.pi*l/k) := by ring
  have hlo : θ<2*Real.pi*l/k-θ := by
    rw [hm]
    have hp : Real.pi/k≤Real.pi*l/k := div_le_div_of_nonneg_right
      (by nlinarith [Real.pi_pos]) hk0.le
    linarith
  by_cases hmid : 2*Real.pi*l/k-θ≤Real.pi
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi hθ hmid hlo
  · have hrefpi : 2*Real.pi-(2*Real.pi*l/k-θ)≤Real.pi := by linarith
    have hreflow : θ<2*Real.pi-(2*Real.pi*l/k-θ) := by
      have hp : Real.pi*l/k≤Real.pi-Real.pi/k := by
        apply (div_le_iff₀ hk0).mpr
        have hcancel : Real.pi/k*k=Real.pi := div_mul_cancel₀ _ (ne_of_gt hk0)
        nlinarith [mul_le_mul_of_nonneg_left hlk Real.pi_pos.le]
      have hπ : 0<Real.pi/k := div_pos Real.pi_pos hk0
      rw [hm]
      linarith
    have hh := Real.cos_lt_cos_of_nonneg_of_le_pi hθ hrefpi hreflow
    simpa only [Real.cos_two_pi_sub] using hh

private theorem polygon_cosine_plus_strict {k : ℕ} (hk : 3≤k) {θ : ℝ}
    (hθ : 0≤θ) (hθk : θ<Real.pi/k) {l : ℕ} (hl0 : 1≤l) (hl : l<k) :
    Real.cos (2*Real.pi*l/k+θ)<Real.cos θ := by
  have hh := polygon_cosine_strict hk hθ hθk (l:=k-l) (by omega) (by omega)
  have hkR : (k:ℝ)≠0 := by exact_mod_cast (show k≠0 by omega)
  have he : 2*Real.pi*(k-l)/k-θ=2*Real.pi-(2*Real.pi*l/k+θ) := by field_simp; ring
  have hcast : ((k-l:ℕ):ℝ)=(k:ℝ)-l := Nat.cast_sub (by omega)
  rw [hcast,he,Real.cos_two_pi_sub] at hh
  exact hh

private theorem trig_residue {j k n : ℕ} (hk : 0<k) :
    Real.cos (n*rationalAngle j k)=Real.cos (2*Real.pi*(((n*j)%k:ℕ):ℝ)/k) ∧
    Real.sin (n*rationalAngle j k)=Real.sin (2*Real.pi*(((n*j)%k:ℕ):ℝ)/k) := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast (ne_of_gt hk)
  have hd : ((n*j:ℕ):ℝ)=((n*j)%k:ℕ)+(k:ℝ)*((n*j)/k:ℕ) := by
    exact_mod_cast (Nat.mod_add_div (n*j) k).symm
  have he : (n:ℝ)*rationalAngle j k=(2*Real.pi*(((n*j)%k:ℕ):ℝ)/k)+((n*j)/k:ℕ)*(2*Real.pi) := by
    dsimp [rationalAngle]
    have hh : (n:ℝ)*j=((n*j)%k:ℕ)+(k:ℝ)*((n*j)/k:ℕ) := by simpa only [Nat.cast_mul] using hd
    field_simp [hkR]
    linear_combination hh
  rw [he,Real.cos_add_nat_mul_two_pi,Real.sin_add_nat_mul_two_pi]
  exact ⟨rfl,rfl⟩

/-- Strict phase locking supplies one feasible growing atom, uniformly for all lags. -/
theorem exists_positive_feasible_of_strict_phase (q : Tuning) {j k : ℕ}
    (hj : 1≤j) (hjk : 2*j<k)
    (hphase : q.angle (rationalAngle j k)<Real.pi/k) :
    ∃ t : ℝ,0<t ∧ Waves.MixtureFeasible (oneAtom (cosineFrequency (rationalAngle j k)))
      (Waves.multiplierMap q.A q.B q.beta t) 0 t ∧
      0<1-Complex.normSq (Waves.multiplierMap q.A q.B q.beta t
        (cosineFrequency (rationalAngle j k))) := by
  let ω := rationalAngle j k
  let c := cosineFrequency ω
  let m := fun t : ℝ=>Waves.multiplierMap q.A q.B q.beta t c
  let g := fun t : ℝ=>1-Complex.normSq (m t)
  let b := fun t : ℝ=>2*(m t).im
  have hω := rationalAngle_mem hj hjk
  have hθ := q.angle_mem hω
  have hk : 3≤k := by omega
  have har : Real.arccos (c:ℝ)=ω := Real.arccos_cos hω.1.le hω.2.le
  have hm0 : m 0=q.m (Waves.z 0 ω) := by change Waves.multiplier _ _ _ _ _=_; rw [har]; rfl
  have hR : 0<q.polarRadius ω := q.polarRadius_pos ⟨hω.1.le,hω.2.le⟩
  have hg0 : 0<g 0 := by
    dsimp [g]
    rw [hm0,q.g_polar ⟨hω.1.le,hω.2.le⟩]
    apply mul_pos hR
    apply Real.cos_pos_of_mem_Ioo
    have hπ : Real.pi/k≤Real.pi/2 := div_le_div_of_nonneg_left Real.pi_pos.le
      (by norm_num) (by exact_mod_cast (show 2≤k by omega))
    exact ⟨by linarith [hθ.1,Real.pi_pos],hphase.trans_le hπ⟩
  let f := fun (t : ℝ) (l : Fin k) (σ : Fin 2)=>
    g t*(1-Real.cos (2*Real.pi*l.val/k))+
      (if σ.val=0 then -1 else 1)*b t*Real.sin (2*Real.pi*l.val/k)
  have hf0 (l : Fin k) (hl : l.val≠0) (σ : Fin 2) : 0<f 0 l σ := by
    have hminus := polygon_cosine_strict hk hθ.1.le hphase (l:=l.val) (by omega) l.isLt
    have hplus := polygon_cosine_plus_strict hk hθ.1.le hphase (l:=l.val) (by omega) l.isLt
    dsimp [f,g,b]
    rw [hm0,q.g_polar ⟨hω.1.le,hω.2.le⟩,q.im_polar ⟨hω.1.le,hω.2.le⟩]
    split_ifs
    · have he : q.polarRadius ω*Real.cos (q.angle ω)*(1-Real.cos (2*Real.pi*l.val/k))+
          (-1:ℝ)*(q.polarRadius ω*Real.sin (q.angle ω))*Real.sin (2*Real.pi*l.val/k)=
          q.polarRadius ω*(Real.cos (q.angle ω)-Real.cos (2*Real.pi*l.val/k-q.angle ω)) := by
        rw [Real.cos_sub]; ring
      rw [he]
      exact mul_pos hR (sub_pos.mpr hminus)
    · have he : q.polarRadius ω*Real.cos (q.angle ω)*(1-Real.cos (2*Real.pi*l.val/k))+
          (1:ℝ)*(q.polarRadius ω*Real.sin (q.angle ω))*Real.sin (2*Real.pi*l.val/k)=
          q.polarRadius ω*(Real.cos (q.angle ω)-Real.cos (2*Real.pi*l.val/k+q.angle ω)) := by
        rw [Real.cos_add]; ring
      rw [he]
      exact mul_pos hR (sub_pos.mpr hplus)
  have hmcont : Continuous m := by
    change Continuous (fun t : ℝ=>Waves.multiplier q.A q.B q.beta t (Real.arccos c))
    unfold Waves.multiplier Waves.z
    have hB : (q.B:ℂ)≠0 := by exact_mod_cast q.B_ne_zero
    fun_prop (disch := aesop)
  have hgcont : Continuous g := by unfold g; fun_prop
  have hbcont : Continuous b := by unfold b; fun_prop
  have hfcont (l : Fin k) (σ : Fin 2) : Continuous (fun t=>f t l σ) := by unfold f; fun_prop
  have hfg (l : Fin k) (σ : Fin 2) : ∀ᶠ t in 𝓝 0,l.val≠0→0<f t l σ := by
    by_cases hl : l.val=0
    · exact Eventually.of_forall (fun _ hn=>False.elim (hn hl))
    · filter_upwards [(hfcont l σ).continuousAt.eventually (eventually_gt_nhds (hf0 l hl σ))] with t ht
      exact fun _=>ht
  have hfinite : ∀ᶠ t in 𝓝 0,∀ l : Fin k,∀ σ : Fin 2,l.val≠0→0<f t l σ := by
    exact Filter.eventually_all.mpr (fun l=>Filter.eventually_all.mpr (hfg l))
  have hevent := (hgcont.continuousAt.eventually (eventually_gt_nhds hg0)).and hfinite
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  let t := ε/2
  have ht : 0<t := by dsimp [t]; positivity
  obtain ⟨hg,hf⟩ := hball (show dist t 0<ε by rw [Real.dist_eq,sub_zero,abs_of_pos ht]; dsimp [t]; linarith)
  refine ⟨t,ht,?_,hg⟩
  rw [oneAtom_feasible_iff]
  refine ⟨by simpa only [g,m,c,ω,abs_zero] using hg.le,fun n hn=>?_⟩
  rw [har]
  obtain ⟨hcos,hsin⟩ := trig_residue (j:=j) (k:=k) (n:=n) (by omega)
  change Real.cos (n*ω)=_ at hcos
  change Real.sin (n*ω)=_ at hsin
  rw [hcos,hsin]
  let l : Fin k := ⟨(n*j)%k,Nat.mod_lt _ (by omega)⟩
  have hfs (σ : Fin 2) : 0≤f t l σ := by
    by_cases hl : l.val=0
    · simp only [f,hl,Nat.cast_zero,mul_zero,zero_div,Real.cos_zero,sub_self,
        Real.sin_zero,add_zero]
      exact le_rfl
    · exact (hf l σ hl).le
  have hp : 0≤g t*(Real.cosh (n*t)-1) := mul_nonneg hg.le (by linarith [Real.one_le_cosh (n*t)])
  have hminus := hfs 0
  have hplus := hfs 1
  simp only [f,Fin.val_zero,Fin.val_one,ite_true,show ¬(1:ℕ)=0 by omega,ite_false] at hminus hplus
  simp only [zero_mul,add_zero,sub_zero]
  change 0≤g t*(Real.cosh (n*t)-Real.cos (2*Real.pi*l.val/k))-b t*Real.sin (2*Real.pi*l.val/k) ∧
    0≤g t*(Real.cosh (n*t)-Real.cos (2*Real.pi*l.val/k))+b t*Real.sin (2*Real.pi*l.val/k)
  constructor <;> nlinarith

/-- Theorem A(ii), strictly inside a rational tongue the actual rate exceeds one. -/
theorem one_lt_rate_of_strict_phase (q : Tuning) {j k : ℕ}
    (hj : 1≤j) (hjk : 2*j<k)
    (hphase : q.angle (rationalAngle j k)<Real.pi/k) : 1<q.rate := by
  obtain ⟨t,ht,hf,hg⟩ := exists_positive_feasible_of_strict_phase q hj hjk hphase
  exact (Real.one_lt_exp_iff.mpr ht).trans_le
    (oneAtom_exp_le_originalRate q _ hf (fun _=>by simpa only [abs_zero] using hg))

end
end polyak.General.Regions
