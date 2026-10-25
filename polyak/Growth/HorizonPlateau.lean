import polyak.Growth.HorizonEnvelope
import polyak.Growth.HorizonExtension
import polyak.Growth.Plateau

/-!
Article: Appendix C, plateau for finite-memory H-segments.
Use: the scalar tail argument applies to infinite H-tables; every finite table
has the proved continuation, and its exact envelope has the proved Fekete infimum.
-/

namespace polyak.Growth.FiniteHorizon
noncomputable section
open Set Filter Finset
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A B β : ℝ} {H : ℕ}

theorem _root_.polyak.Growth.HRun.norm_le_envelope (r : HRun E A B β H) (k : ℕ) :
    ‖r.x k‖  ≤  envelope A B β H k*stateNorm r.x 0 :=
  (norm_left_le_stateNorm r.x k).trans (stateNorm_le_envelope_hilbert (r.segment k))

theorem _root_.polyak.Growth.HRun.discountedEnergy_subexponential (hB : B≠0) (r : HRun E A B β H) :
    Subexponential (discountedEnergy r.x (Real.log (growthRate A B β H))) := by
  intro δ hδ
  let t := Real.log (growthRate A B β H)
  let R := Real.exp (t+δ/2)
  have hR : growthRate A B β H < R := by
    rw [← Real.exp_log (growthRate_pos A B β H)]
    exact Real.exp_lt_exp.mpr (by dsimp [t]; linarith)
  obtain ⟨C,hC,hbound⟩ := exists_envelope_le_mul_pow hB hR
  let D := C*stateNorm r.x 0
  have hD : 0  ≤  D := mul_nonneg hC.le (stateNorm_nonneg r.x 0)
  refine ⟨D^2+1, by positivity, fun k => ?_⟩
  have hx : ‖r.x k‖  ≤  D*Real.exp ((k : ℝ)*(t+δ/2)) := by
    let s := r.segment k
    have hg := stateNorm_le_envelope_hilbert s
    have hnorm := norm_left_le_stateNorm r.x k
    calc
      ‖r.x k‖  ≤  stateNorm r.x k := hnorm
      _  ≤  envelope A B β H k * stateNorm r.x 0 := hg
      _  ≤  (C*R^k)*stateNorm r.x 0 := by
        exact mul_le_mul_of_nonneg_right (hbound k) (stateNorm_nonneg r.x 0)
      _ = D*Real.exp ((k : ℝ)*(t+δ/2)) := by
        dsimp [D, R]
        rw [← Real.exp_nat_mul]
        ring
  have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD (Real.exp_pos _).le)).mpr hx
  have he : Real.exp (-2*(k : ℝ)*t)*(D*Real.exp ((k : ℝ)*(t+δ/2)))^2 =
      D^2*Real.exp (δ*k) := by
    calc
      _ = D^2*(Real.exp (-2*(k : ℝ)*t)*Real.exp ((k : ℝ)*(t+δ/2))*
          Real.exp ((k : ℝ)*(t+δ/2))) := by ring
      _ = D^2*Real.exp ((-2*(k : ℝ)*t+(k : ℝ)*(t+δ/2))+(k : ℝ)*(t+δ/2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ = _ := by congr 2; ring
  change Real.exp (-2*(k : ℝ)*t)*‖r.x k‖^2  ≤  _
  calc
    _  ≤  Real.exp (-2*(k : ℝ)*t)*(D*Real.exp ((k : ℝ)*(t+δ/2)))^2 :=
      mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = D^2*Real.exp (δ*k) := he
    _  ≤  (D^2+1)*Real.exp (δ*k) := by nlinarith [Real.exp_pos (δ*k)]


def boundaryConstant (A B β t : ℝ) (H m : ℕ) : ℝ :=
  1+∑ k∈Ico 0 m,Real.exp (-2*k*t)*envelope A B β H k^2

theorem boundaryConstant_pos (A B β t : ℝ) (H m : ℕ) :
    0<boundaryConstant A B β t H m := by
  have hh : 0 ≤ ∑ k∈Ico 0 m,Real.exp (-2*k*t)*envelope A B β H k^2 :=
    sum_nonneg (fun _ _ => by positivity)
  dsimp only [boundaryConstant]
  linarith

theorem _root_.polyak.Growth.HRun.mass_le_boundaryConstant (r : HRun E A B β H) (t : ℝ) (m : ℕ) :
    mass (discountedEnergy r.x t) 0 m  ≤  boundaryConstant A B β t H m*stateNorm r.x 0^2 := by
  calc
    _  ≤  ∑ k ∈ Ico 0 m, (Real.exp (-2*k*t)*envelope A B β H k^2)*stateNorm r.x 0^2 := by
      apply sum_le_sum
      intro k _
      have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (envelope_nonneg A B β H k)
        (stateNorm_nonneg r.x 0))).mpr (r.norm_le_envelope k)
      have hw := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-2*k*t)).le
      simpa only [discountedEnergy, mul_pow, mul_assoc] using hw
    _ = (∑ k ∈ Ico 0 m, Real.exp (-2*k*t)*envelope A B β H k^2)*stateNorm r.x 0^2 :=
      (sum_mul _ _ _).symm
    _  ≤  _ := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      dsimp [boundaryConstant]
      linarith


def WindowEnergyBound (A B β t K : ℝ) (H w : ℕ) : Prop :=
  ∀ d : ℕ,∀ r : HRun (EuclideanSpace ℝ (Fin d)) A B β H,∀ i j : ℕ,
    w ≤ i → i ≤ j → mass (discountedEnergy r.x t) i (j+1)  ≤ 
      K*(energyWindow (discountedEnergy r.x t) w i+energyWindow (discountedEnergy r.x t) w j)

theorem windowEnergyBound_tail {K : ℝ} {w : ℕ} (hB : B≠0) (hK : 0<K)
    (henergy : WindowEnergyBound A B β (Real.log (growthRate A B β H)) K H w) :
    ∃ D : ℝ,1<D ∧ ∀ d : ℕ,∀ r : HRun (EuclideanSpace ℝ (Fin d)) A B β H,
      ∀ i j : ℕ,i ≤ j → mass (discountedEnergy r.x (Real.log (growthRate A B β H))) i j  ≤ 
        D*(discountedEnergy r.x (Real.log (growthRate A B β H)) i+
          discountedEnergy r.x (Real.log (growthRate A B β H)) (i+1)) := by
  let t := Real.log (growthRate A B β H)
  let C := (1+2*K)*boundaryConstant A B β t H (2*w+1)
  have hC : 0 < C := mul_pos (by linarith) (boundaryConstant_pos _ _ _ _ _ _)
  let D := 2+C*(1+Real.exp (2*t))
  have hD : 1 < D := by
    dsimp [D]
    nlinarith [mul_pos hC (show 0 < 1+Real.exp (2*t) by positivity)]
  refine ⟨D,hD,fun d r i j hij => ?_⟩
  let q := r.shift i
  have hsub := HRun.discountedEnergy_subexponential hB q
  have hmass := mass_zero_le_boundary (discountedEnergy_nonneg q.x t) hsub hK w
    (fun l hl => henergy d q w l le_rfl hl) (j-i)
  have hbound := q.mass_le_boundaryConstant t (2*w+1)
  have hs : mass (discountedEnergy q.x t) 0 (j-i)  ≤  C*stateNorm q.x 0^2 := by
    calc
      _  ≤  (1+2*K)*mass (discountedEnergy q.x t) 0 (2*w+1) := hmass
      _  ≤  (1+2*K)*(boundaryConstant A B β t H (2*w+1)*stateNorm q.x 0^2) :=
        mul_le_mul_of_nonneg_left hbound (by linarith)
      _ = _ := by dsimp [C]; ring
  have hshift : mass (discountedEnergy q.x t) 0 (j-i) =
      Real.exp (2*i*t)*mass (discountedEnergy r.x t) i j := by
    change mass (discountedEnergy (fun k => r.x (i+k)) t) 0 (j-i) = _
    rw [mass_discountedEnergy_shift, Nat.add_sub_of_le hij]
  rw [hshift] at hs
  have hcancel : Real.exp (-2*i*t)*Real.exp (2*i*t) = 1 := by
    rw [← Real.exp_add]
    have he : -2*(i : ℝ)*t+2*i*t=0 := by ring
    rw [he, Real.exp_zero]
  have hstate : Real.exp (-2*i*t)*stateNorm q.x 0^2 =
      discountedEnergy r.x t i+Real.exp (2*t)*discountedEnergy r.x t (i+1) := by
    have hx : stateNorm q.x 0 = stateNorm r.x i := by simp [q, HRun.shift, stateNorm]
    rw [hx, discounted_stateNorm]
  have hb₀ := discountedEnergy_nonneg r.x t i
  have hb₁ := discountedEnergy_nonneg r.x t (i+1)
  calc
    mass (discountedEnergy r.x t) i j =
        Real.exp (-2*i*t)*(Real.exp (2*i*t)*mass (discountedEnergy r.x t) i j) := by
      rw [← mul_assoc, hcancel, one_mul]
    _  ≤  Real.exp (-2*i*t)*(C*stateNorm q.x 0^2) :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    _ = C*(discountedEnergy r.x t i+Real.exp (2*t)*discountedEnergy r.x t (i+1)) := by
      rw [mul_left_comm, hstate]
    _  ≤  D*(discountedEnergy r.x t i+discountedEnergy r.x t (i+1)) := by
      dsimp [D]
      nlinarith [mul_nonneg (Real.exp_pos (2*t)).le hb₀,
        mul_nonneg hC.le hb₀, mul_nonneg hC.le hb₁,
        mul_nonneg hC.le (mul_nonneg (Real.exp_pos (2*t)).le hb₀)]


theorem not_uniform_mass_bound {D : ℝ} (hB : B≠0) (hD : 1<D)
    (hbound : ∀ d : ℕ,∀ r : HRun (EuclideanSpace ℝ (Fin d)) A B β H,
      ∀ i j : ℕ,i ≤ j → mass (discountedEnergy r.x (Real.log (growthRate A B β H))) i j  ≤ 
        D*(discountedEnergy r.x (Real.log (growthRate A B β H)) i+
          discountedEnergy r.x (Real.log (growthRate A B β H)) (i+1))) : False := by
  let t := Real.log (growthRate A B β H)
  let θ := 1-1/D
  let Cstate := (1+Real.exp (2*t))*D*(1+Real.exp (-2*t))
  have hDp : 0 < D := zero_lt_one.trans hD
  have hθ0 : 0  ≤  θ := by
    dsimp [θ]
    have hh := (div_le_one hDp).2 hD.le
    linarith
  have hθ1 : θ < 1 := by
    dsimp [θ]
    linarith [one_div_pos.mpr hDp]
  have hH : 0 < Cstate := by dsimp [Cstate]; positivity
  have hlim : Tendsto (fun p : ℕ => Cstate*θ^p) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul Cstate
  obtain ⟨p,hp,hp0⟩ := ((hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))).and
    (eventually_gt_atTop 0)).exists
  have hsegment {d : ℕ} (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H (2*p)) :
      stateNorm s.x (2*p)  ≤  (1/2 : ℝ)*Real.exp ((2*p : ℕ)*t)*stateNorm s.x 0 := by
    obtain ⟨r,hr,_⟩ := s.exists_hRun
    have hpair := pair_le_geometric (discountedEnergy_nonneg r.x t) hD (hbound d r) p
    have hs := discounted_state_le_pair r.x t (2*p)
    have hinit := discounted_pair_zero_le_state r.x t
    have hraw : Real.exp (-2*(2*p : ℕ)*t)*stateNorm r.x (2*p)^2  ≤ 
        Cstate*θ^p*stateNorm r.x 0^2 := by
      calc
        _  ≤  (1+Real.exp (2*t))*(discountedEnergy r.x t (2*p)+
            discountedEnergy r.x t (2*p+1)) := hs
        _  ≤  (1+Real.exp (2*t))*(θ^p*D*(discountedEnergy r.x t 0+
            discountedEnergy r.x t 1)) :=
          mul_le_mul_of_nonneg_left hpair (by positivity)
        _  ≤  (1+Real.exp (2*t))*(θ^p*D*((1+Real.exp (-2*t))*stateNorm r.x 0^2)) := by
          gcongr
        _ = _ := by dsimp [Cstate]; ring
    have he : Real.exp (2*(2*p : ℕ)*t)*Real.exp (-2*(2*p : ℕ)*t) = 1 := by
      rw [← Real.exp_add]
      have hz : 2*(↑(2*p) : ℝ)*t + -2*(↑(2*p) : ℝ)*t = 0 := by ring
      rw [hz, Real.exp_zero]
    have he2 : Real.exp (2*(2*p : ℕ)*t) = Real.exp ((2*p : ℕ)*t)^2 := by
      calc
        _ = Real.exp (((2*p : ℕ) : ℝ)*t+((2*p : ℕ) : ℝ)*t) := by congr 1; ring
        _ = _ := by rw [Real.exp_add, pow_two]
    have hm := mul_le_mul_of_nonneg_left hraw (Real.exp_pos (2*(2*p : ℕ)*t)).le
    rw [← mul_assoc, he, one_mul, he2] at hm
    have hsq : stateNorm r.x (2*p)^2  ≤ 
        ((1/2 : ℝ)*Real.exp ((2*p : ℕ)*t)*stateNorm r.x 0)^2 := by
      have hsmall : Cstate*θ^p  ≤  (1/4 : ℝ) := hp.le
      have hnon : 0  ≤  Real.exp ((2*p : ℕ)*t)^2*stateNorm r.x 0^2 := by positivity
      have hh := mul_le_mul_of_nonneg_right hsmall hnon
      nlinarith [hm]
    have hnon : 0  ≤  (1/2 : ℝ)*Real.exp ((2*p : ℕ)*t)*stateNorm r.x 0 :=
      mul_nonneg (by positivity) (stateNorm_nonneg _ _)
    have hn := (sq_le_sq₀ (stateNorm_nonneg r.x (2*p)) hnon).mp hsq
    have hnorm (k : ℕ) (hk : k  ≤  2*p) : stateNorm r.x k = stateNorm s.x k := by
      simp only [stateNorm, hr k (by omega), hr (k+1) (by omega)]
    simpa only [hnorm (2*p) le_rfl, hnorm 0 (by omega)] using hn
  have hΓ : envelope A B β H (2*p)  ≤  (1/2 : ℝ)*Real.exp ((2*p : ℕ)*t) := by
    apply csSup_le (insert_nonempty _ _)
    intro v hv
    rcases hv with rfl | ⟨d,s,hs,rfl⟩
    · positivity
    · apply (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hs))).2
      exact hsegment s
  have hlo := growthRate_pow_le_envelope (A := A) (β := β) hB H (2*p)
  have hexp : growthRate A B β H^(2*p) = Real.exp ((2*p : ℕ)*t) := by
    rw [← Real.exp_log (growthRate_pos A B β H), ← Real.exp_nat_mul]
  rw [hexp] at hlo
  linarith [Real.exp_pos ((2*p : ℕ)*t)]


/-- Article: no uniform finite-window energy inequality holds at the exact H-segment rate. -/
theorem not_windowEnergyBound_at_growth {K : ℝ} {w : ℕ} (hB : B≠0) (hK : 0<K) :
    ¬WindowEnergyBound A B β (Real.log (growthRate A B β H)) K H w := by
  intro henergy
  obtain ⟨D,hD,hbound⟩ := windowEnergyBound_tail hB hK henergy
  exact not_uniform_mass_bound hB hD hbound

end
end polyak.Growth.FiniteHorizon
