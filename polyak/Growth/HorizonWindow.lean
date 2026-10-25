import polyak.Growth.HorizonEnvelope

/-!
Article: Appendix C, equation (windowgrowth), with the state convention S_k=(e_k,e_{k+1}).
Use: the trace of a Gram window has the same asymptotic rate as the free state;
the finite maximum is taken over the appropriate bounded tail of Γ_H.
-/

namespace polyak.Growth.FiniteHorizon
noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

/-- Article: trace of the Gram matrix of e_{k−H},…,e_{k+1}. -/
def windowTrace (x : ℕ → E) (H k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc (k-H) (k+1),‖x i‖^2

theorem windowTrace_nonneg (x : ℕ → E) (H k : ℕ) : 0 ≤ windowTrace x H k :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem norm_sq_le_windowTrace (x : ℕ → E) {H k i : ℕ}
    (hi : k-H ≤ i) (hik : i ≤ k+1) : ‖x i‖^2 ≤ windowTrace x H k := by
  unfold windowTrace
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖x j‖) (Finset.mem_Icc.mpr ⟨hi,hik⟩)

/-- Article: a Gram trace contains both components of the free state. -/
theorem stateNorm_sq_le_windowTrace (x : ℕ → E) (H k : ℕ) :
    stateNorm x k^2 ≤ windowTrace x H k := by
  classical
  have hsub : ({k,k+1} : Finset ℕ) ⊆ Finset.Icc (k-H) (k+1) := by
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> simp only [Finset.mem_Icc] <;> omega
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun i _ _ => sq_nonneg ‖x i‖)
  rw [Finset.sum_pair (by omega : k≠k+1)] at hs
  exact (stateNorm_sq x k).le.trans hs

/-- Article: index set for the bounded tail of Γ_H under the chosen two-position state convention. -/
def windowIndices (H p : ℕ) : Finset ℕ := Finset.Icc (p-H-1) p

theorem windowIndices_nonempty (H p : ℕ) : (windowIndices H p).Nonempty :=
  ⟨p,Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩⟩

/-- Article: the finite maximum of squared free-state bounds needed for the whole window. -/
def windowFactor (A B β : ℝ) (H p : ℕ) : ℝ :=
  (windowIndices H p).sup' (windowIndices_nonempty H p) (fun i => envelope A B β H i^2)

theorem envelope_sq_le_windowFactor (A B β : ℝ) {H p i : ℕ}
    (hi : p-H-1 ≤ i) (hip : i ≤ p) :
    envelope A B β H i^2 ≤ windowFactor A B β H p :=
  Finset.le_sup' (fun i => envelope A B β H i^2) (Finset.mem_Icc.mpr ⟨hi,hip⟩)

theorem one_le_windowFactor (A B β : ℝ) {H p : ℕ} (hp : p ≤ H) :
    1 ≤ windowFactor A B β H p := by
  have hh := envelope_sq_le_windowFactor A B β (H:=H) (p:=p) (i:=0) (by omega) (Nat.zero_le _)
  simpa only [envelope_zero,one_pow] using hh

/-- Article: exact finite-window growth for every admissible H-segment.
The shift by one in the lower cutoff reflects S_k=(e_k,e_{k+1}). -/
theorem windowTrace_add_le [InnerProductSpace ℝ E] {A B β : ℝ} {H n : ℕ} (s : HSegment E A B β H n)
    (k p : ℕ) (hk : H ≤ k) (hkp : k+p ≤ n) :
    windowTrace s.x H (k+p) ≤ (H+2 : ℝ)*windowFactor A B β H p*windowTrace s.x H k := by
  have htrace := windowTrace_nonneg s.x H k
  have hterm (i : ℕ) (hi : i∈Finset.Icc (k+p-H) (k+p+1)) :
      ‖s.x i‖^2 ≤ windowFactor A B β H p*windowTrace s.x H k := by
    have hleft := (Finset.mem_Icc.mp hi).1
    have hright := (Finset.mem_Icc.mp hi).2
    by_cases hik : i ≤ k
    · have hpH : p ≤ H := by omega
      have hnorm := norm_sq_le_windowTrace s.x (H:=H) (k:=k) (i:=i) (by omega) (by omega)
      have hfac := one_le_windowFactor A B β hpH
      nlinarith
    · let j := i-1
      let r := j-k
      have hkr : k+r=j := by dsimp only [r,j]; omega
      have hri : p-H-1 ≤ r := by dsimp only [r,j]; omega
      have hrp : r ≤ p := by dsimp only [r,j]; omega
      have hfac := envelope_sq_le_windowFactor A B β hri hrp
      have hstate := stateNorm_window_le_envelope s k r (by rw [hkr]; dsimp only [j]; omega)
      rw [hkr] at hstate
      have hnorm : ‖s.x i‖ ≤ stateNorm s.x j := by
        have hh := norm_right_le_stateNorm s.x j
        simpa only [show j+1=i by dsimp only [j]; omega] using hh
      have hsq : ‖s.x i‖^2 ≤ (envelope A B β H r*stateNorm s.x k)^2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (envelope_nonneg A B β H r)
          (stateNorm_nonneg s.x k))).mpr (hnorm.trans hstate)
      have hstateTrace := stateNorm_sq_le_windowTrace s.x H k
      calc
        ‖s.x i‖^2 ≤ (envelope A B β H r*stateNorm s.x k)^2 := hsq
        _=envelope A B β H r^2*stateNorm s.x k^2 := mul_pow _ _ _
        _≤windowFactor A B β H p*windowTrace s.x H k :=
          mul_le_mul hfac hstateTrace (sq_nonneg _) (by
            exact (sq_nonneg (envelope A B β H r)).trans hfac)
  have hcard : (Finset.Icc (k+p-H) (k+p+1)).card=H+2 := by
    rw [Nat.card_Icc]
    omega
  calc
    windowTrace s.x H (k+p) ≤
        ∑ _i ∈ Finset.Icc (k+p-H) (k+p+1),windowFactor A B β H p*windowTrace s.x H k :=
      Finset.sum_le_sum hterm
    _=(H+2 : ℝ)*windowFactor A B β H p*windowTrace s.x H k := by
      rw [Finset.sum_const,hcard,nsmul_eq_mul]
      push_cast
      ring

end
end polyak.Growth.FiniteHorizon
