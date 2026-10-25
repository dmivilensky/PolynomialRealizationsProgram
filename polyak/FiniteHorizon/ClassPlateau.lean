import polyak.FiniteHorizon.ClassContraction

/-!
Article: Appendix C, Lemma plateauclass for arbitrary restriction-closed classes.
Use: a finite-window energy estimate at the positive root-limit exponent is
impossible. The proof iterates contraction only while a finite suffix remains.
-/
noncomputable section
namespace polyak.FiniteHorizon.SegmentClass
open Growth Growth.FiniteHorizon Set Filter Finset
open scoped Topology
variable {A B β : ℝ} {H : ℕ} (G : SegmentClass A B β H)

theorem not_energyBound_at_rate {r K : ℝ} {w : ℕ}
    (hpos : ∀ n,0<G.envelope n) (hr : 0<r)
    (hlim : Tendsto (fun n : ℕ => G.envelope n^((n : ℝ)⁻¹)) atTop (𝓝 r))
    (hK : 0<K) : ¬G.EnergyBound (Real.log r) K w := by
  intro he
  obtain ⟨P,N,hP,hPN,hcontract⟩:=G.exists_long_prefix_contraction hpos hr hlim hK he
  have hN : 0<N:=by omega
  have hstep {d n : ℕ} (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n)
      (hn : N≤n) (hs : G.contains d n s) :
      stateNorm s.x P≤(3/4 : ℝ)*r^P*stateNorm s.x 0 := by
    have hh:=hcontract d n s hn hs
    have hcancel : Real.exp (2*(P : ℝ)*Real.log r)*Real.exp (-2*(P : ℝ)*Real.log r)=1:=by
      rw [←Real.exp_add]
      simp
    have hpow : Real.exp (2*(P : ℝ)*Real.log r)=(r^P)^2:=by
      rw [←Real.exp_log hr,←Real.exp_nat_mul]
      rw [show 2*(P : ℝ)*Real.log (Real.exp (Real.log r))=
        (P : ℝ)*Real.log r+(P : ℝ)*Real.log r by rw [Real.log_exp]; ring,Real.exp_add,pow_two]
    have hm:=mul_le_mul_of_nonneg_left hh (Real.exp_pos (2*(P : ℝ)*Real.log r)).le
    rw [←mul_assoc,hcancel,one_mul,hpow] at hm
    have hright : 0≤(3/4 : ℝ)*r^P*stateNorm s.x 0:=
      mul_nonneg (by positivity) (stateNorm_nonneg s.x 0)
    apply (sq_le_sq₀ (stateNorm_nonneg s.x P) hright).mp
    rw [mul_pow,mul_pow]
    nlinarith [mul_nonneg (sq_nonneg (r^P)) (sq_nonneg (stateNorm s.x 0))]
  have hprefix (q : ℕ) {d n : ℕ} (s : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n)
      (hn : N+q*P≤n) (hs : G.contains d n s) :
      stateNorm s.x (q*P)≤((3/4 : ℝ)*r^P)^q*stateNorm s.x 0:=by
    induction q with
    | zero => simp
    | succ q ih =>
      simp only [Nat.add_mul,Nat.one_mul] at hn
      let tail:=s.restrict (q*P) (n-q*P) (by omega)
      have htail : G.contains d (n-q*P) tail:=G.restriction d n s hs _ _ _
      have ht:=hstep tail (by omega) htail
      simp only [tail,HSegment.stateNorm_restrict,Nat.add_zero] at ht
      have hi:=ih (by omega)
      have hm:=mul_le_mul_of_nonneg_left hi (show 0≤(3/4 : ℝ)*r^P by positivity)
      calc
        _=stateNorm s.x (q*P+P):=by rw [Nat.succ_mul]
        _≤(3/4 : ℝ)*r^P*stateNorm s.x (q*P):=ht
        _≤(3/4 : ℝ)*r^P*(((3/4 : ℝ)*r^P)^q*stateNorm s.x 0):=hm
        _=_:=by rw [pow_succ]; ring
  have hupper (q : ℕ) : G.envelope (N+q*P)≤G.envelope N*((3/4 : ℝ)*r^P)^q:=by
    apply csSup_le (Set.insert_nonempty _ _)
    rintro v (rfl|⟨d,s,hs,hzero,rfl⟩)
    · exact mul_nonneg (G.envelope_nonneg N) (by positivity)
    · apply (div_le_iff₀ (lt_of_le_of_ne (stateNorm_nonneg s.x 0) (Ne.symm hzero))).mpr
      have htail:=G.stateNorm_window_le s hs (q*P) N (by omega)
      have hpref:=hprefix q s le_rfl hs
      have hm:=mul_le_mul_of_nonneg_left hpref (G.envelope_nonneg N)
      have hh : stateNorm s.x (N+q*P)≤G.envelope N*((3/4 : ℝ)*r^P)^q*stateNorm s.x 0:=by
        calc
          _=stateNorm s.x (q*P+N):=by congr 1; omega
          _≤G.envelope N*stateNorm s.x (q*P):=htail
          _≤G.envelope N*(((3/4 : ℝ)*r^P)^q*stateNorm s.x 0):=hm
          _=_:=by ring
      exact hh
  have hbound (q : ℕ) : r^N≤G.envelope N*(3/4 : ℝ)^q:=by
    have hl:=G.rate_pow_le hpos hr hlim (N+q*P) (by omega)
    have hh:=hl.trans (hupper q)
    rw [pow_add,mul_pow,←pow_mul,show P*q=q*P from Nat.mul_comm _ _] at hh
    apply (mul_le_mul_iff_right₀ (pow_pos hr (q*P))).mp
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh
  have hz : r^N≤0:=by
    have hl : Tendsto (fun q : ℕ => G.envelope N*(3/4 : ℝ)^q) atTop (𝓝 0):=by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤3/4)
        (by norm_num : (3/4 : ℝ)<1)).const_mul (G.envelope N)
    exact ge_of_tendsto hl (Eventually.of_forall hbound)
  exact (not_le_of_gt (pow_pos hr N)) hz

end polyak.FiniteHorizon.SegmentClass
