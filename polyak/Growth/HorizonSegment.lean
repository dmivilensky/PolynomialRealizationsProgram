import polyak.Growth.Completion
import polyak.Growth.Extension
import Mathlib.Data.Nat.Dist

/-!
Article: Appendix C, finite-memory H-segments and continuation of every admissible window.
Use: retain precisely the article's interior data, all minimizer inequalities,
and only interpolation pairs at distance at most H. No endpoint gradients are required.
-/

namespace polyak.Growth
noncomputable section
open Interpolation

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: a literal H-segment, with n transitions and n interior data points. -/
structure HSegment (A B β : ℝ) (H n : ℕ) where
  x : ℕ → E
  σ : ℕ → E
  value : ℕ → ℝ
  interpolation : ∀ i,1 ≤ i → i ≤ n → ∀ j,1 ≤ j → j ≤ n → Nat.dist i j ≤ H →
    |datumT x σ value i j| ≤ datumR x σ i j
  origin : ∀ i,1 ≤ i → i ≤ n → |value i-(1/2 : ℝ)*inner ℝ (σ i) (x i)| ≤ 
    (1/4 : ℝ)*(‖x i‖^2-‖σ i‖^2)
  recurrence : ∀ k,k<n → x (k+2)=A • x (k+1)+B • σ (k+1)-β • x k

variable {E}
namespace HSegment
variable {A B β : ℝ} {H n : ℕ}

/-- Article: ordinary segments obey every finite-memory relaxation. -/
def ofSegment (s : Segment E A B β n) (H : ℕ) : HSegment E A B β H n where
  x := s.x
  σ := s.σ
  value := s.value
  interpolation i _ hi j _ hj _ := s.interpolation i (by omega) j (by omega)
  origin i _ hi := s.origin i (by omega)
  recurrence := s.recurrence

/-- Article: restricting consecutive positions preserves the exact memory bound. -/
def restrict (s : HSegment E A B β H n) (l m : ℕ) (h : l+m ≤ n) :
    HSegment E A B β H m where
  x k := s.x (l+k)
  σ k := s.σ (l+k)
  value k := s.value (l+k)
  interpolation i hi him j hj hjm hij := s.interpolation (l+i) (by omega) (by omega)
    (l+j) (by omega) (by omega) (by rwa [Nat.dist_add_add_left])
  origin i hi him := s.origin (l+i) (by omega) (by omega)
  recurrence k hk := by simpa only [Nat.add_assoc] using s.recurrence (l+k) (by omega)

theorem stateNorm_restrict (s : HSegment E A B β H n) (l m : ℕ) (h : l+m ≤ n) (k : ℕ) :
    stateNorm (s.restrict l m h).x k=stateNorm s.x (l+k) := by
  simp [stateNorm,restrict,Nat.add_assoc]

/-- Article: increasing the retained memory only adds restrictions. -/
def weaken (s : HSegment E A B β H n) (h : ℕ) (hh : h ≤ H) : HSegment E A B β h n where
  x := s.x
  σ := s.σ
  value := s.value
  interpolation i hi hin j hj hjn hij := s.interpolation i hi hin j hj hjn (hij.trans hh)
  origin := s.origin
  recurrence := s.recurrence

/-- Article: the minimizer inequalities alone give the gradient bound. -/
theorem norm_gradient_le (s : HSegment E A B β H n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ‖s.σ i‖ ≤ ‖s.x i‖ := by
  have h := le_trans (abs_nonneg _) (s.origin i hi hin)
  nlinarith [norm_nonneg (s.σ i),norm_nonneg (s.x i)]

/-- Article: every admissible value is controlled by half the squared position norm. -/
theorem abs_value_le (s : HSegment E A B β H n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    |s.value i| ≤ ‖s.x i‖^2/2 := by
  have hstar := s.origin i hi hin
  have hinner := abs_real_inner_le_norm (s.σ i) (s.x i)
  have habs : |s.value i| ≤ |s.value i-(1/2 : ℝ)*inner ℝ (s.σ i) (s.x i)|+
      (1/2 : ℝ)*|inner ℝ (s.σ i) (s.x i)| := by
    have hh := abs_add_le (s.value i-(1/2 : ℝ)*inner ℝ (s.σ i) (s.x i))
      ((1/2 : ℝ)*inner ℝ (s.σ i) (s.x i))
    simpa only [sub_add_cancel,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)] using hh
  nlinarith [sq_nonneg (‖s.x i‖-‖s.σ i‖)]

/-- Article: the elementary comparison estimate needs no long-range interpolation. -/
theorem stateNorm_succ_le (s : HSegment E A B β H n) (k : ℕ) (hk : k<n) :
    stateNorm s.x (k+1) ≤ (1+|A|+|B|+|β|)*stateNorm s.x k := by
  have hx := norm_right_le_stateNorm s.x k
  have hy := norm_left_le_stateNorm s.x k
  have hσ := s.norm_gradient_le (k+1) (by omega) (by omega)
  have ht : ‖s.x (k+2)‖ ≤ (|A|+|B|+|β|)*stateNorm s.x k := by
    rw [s.recurrence k hk]
    calc
      ‖A • s.x (k+1)+B • s.σ (k+1)-β • s.x k‖ ≤ 
          ‖A • s.x (k+1)‖+‖B • s.σ (k+1)‖+‖β • s.x k‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ = |A| *‖s.x (k+1)‖+|B| *‖s.σ (k+1)‖+|β| *‖s.x k‖ := by
        simp only [norm_smul,Real.norm_eq_abs]
      _ ≤ |A| *stateNorm s.x k+|B| *stateNorm s.x k+|β| *stateNorm s.x k := by
        gcongr
        exact hσ.trans hx
      _ = _ := by ring
  have hz := stateNorm_sq s.x (k+1)
  have hstate := stateNorm_nonneg s.x k
  have hnext := stateNorm_nonneg s.x (k+1)
  have hc : 0 ≤ |A|+|B|+|β| := by positivity
  have hs : 0 ≤ (|A|+|B|+|β|)*stateNorm s.x k := mul_nonneg hc hstate
  have hxx := (sq_le_sq₀ (norm_nonneg _) hstate).mpr hx
  have htt := (sq_le_sq₀ (norm_nonneg _) hs).mpr ht
  rw [show k+1+1=k+2 by omega] at hz
  nlinarith [mul_nonneg hc (sq_nonneg (stateNorm s.x k))]

theorem stateNorm_le (s : HSegment E A B β H n) (k : ℕ) (hk : k ≤ n) :
    stateNorm s.x k ≤ (1+|A|+|B|+|β|)^k*stateNorm s.x 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ ≤ (1+|A|+|B|+|β|)*stateNorm s.x k := s.stateNorm_succ_le k (by omega)
      _ ≤ (1+|A|+|B|+|β|)*((1+|A|+|B|+|β|)^k*stateNorm s.x 0) := by
        gcongr
        exact ih (by omega)
      _ = _ := by rw [pow_succ]; ring

theorem stateNorm_eq_zero_of_zero (s : HSegment E A B β H n)
    (h : stateNorm s.x 0=0) (k : ℕ) (hk : k ≤ n) : stateNorm s.x k=0 := by
  have hh := s.stateNorm_le k hk
  rw [h,mul_zero] at hh
  exact le_antisymm hh (stateNorm_nonneg s.x k)

/-- Article: each window of at most H+1 interior data has all interpolation pairs. -/
def raw (s : HSegment E A B β H n) (hn : n ≤ H+1) : RawSegment E A B β n where
  x := s.x
  σ := s.σ
  value := s.value
  interpolation i hi hin j hj hjn := s.interpolation i hi hin j hj hjn (by
    unfold Nat.dist
    omega)
  origin := s.origin
  recurrence := s.recurrence

/-- Article: linear isometries preserve every finite-memory constraint. -/
def map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (s : HSegment E A B β H n) (J : E →ₗᵢ[ℝ] F) : HSegment F A B β H n where
  x k := J (s.x k)
  σ k := J (s.σ k)
  value := s.value
  interpolation i hi hin j hj hjn hij := by
    simpa only [datumT_isometry,datumR_isometry] using s.interpolation i hi hin j hj hjn hij
  origin i hi hin := by simpa only [J.inner_map_map,J.norm_map] using s.origin i hi hin
  recurrence k hk := by
    simpa only [map_sub,map_add,map_smul] using congrArg J (s.recurrence k hk)

theorem stateNorm_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (s : HSegment E A B β H n) (J : E →ₗᵢ[ℝ] F) (k : ℕ) :
    stateNorm (s.map J).x k=stateNorm s.x k := by simp [stateNorm,map]

/-- Article: compression uses the finite span of the actual positions and gradients. -/
def inSpan (s : HSegment E A B β H n) :
    HSegment (dataSpan (fun i : Fin (n+2) => s.x i) (fun i : Fin (n+2) => s.σ i)) A B β H n where
  x k := spanPosition (fun i : Fin (n+2) => s.x i) (fun i : Fin (n+2) => s.σ i)
    (Segment.finiteIndex n k)
  σ k := spanGradient (fun i : Fin (n+2) => s.x i) (fun i : Fin (n+2) => s.σ i)
    (Segment.finiteIndex n k)
  value k := s.value (Segment.finiteIndex n k)
  interpolation i hi hin j hj hjn hij := by
    simpa only [datumT,datumR,spanPosition,spanGradient,Segment.finiteIndex,
      min_eq_left (show i ≤ n+1 by omega),min_eq_left (show j ≤ n+1 by omega),
      ← Submodule.norm_coe,Submodule.coe_inner,Submodule.coe_add,Submodule.coe_sub] using
      s.interpolation i hi hin j hj hjn hij
  origin i hi hin := by
    simpa only [spanPosition,spanGradient,Segment.finiteIndex,min_eq_left (show i ≤ n+1 by omega),
      ← Submodule.norm_coe,Submodule.coe_inner,Submodule.coe_add,Submodule.coe_sub] using s.origin i hi hin
  recurrence k hk := by
    apply Subtype.ext
    change s.x (min (k+2) (n+1))=A • s.x (min (k+1) (n+1))+
      B • s.σ (min (k+1) (n+1))-β • s.x (min k (n+1))
    simpa only [min_eq_left (show k+2 ≤ n+1 by omega),min_eq_left (show k+1 ≤ n+1 by omega),
      min_eq_left (show k ≤ n+1 by omega)] using s.recurrence k hk

theorem stateNorm_inSpan (s : HSegment E A B β H n) (k : ℕ) (hk : k ≤ n) :
    stateNorm s.inSpan.x k=stateNorm s.x k := by
  simp only [stateNorm,inSpan,spanPosition,Segment.finiteIndex,← Submodule.norm_coe,
    min_eq_left (show k ≤ n+1 by omega),min_eq_left (show k+1 ≤ n+1 by omega)]

/-- Article: arbitrary Hilbert-space tables give exactly finite-dimensional growth ratios. -/
theorem exists_euclidean (s : HSegment E A B β H n) :
    ∃ d : ℕ,∃ q : HSegment (EuclideanSpace ℝ (Fin d)) A B β H n,
      ∀ k,k ≤ n → stateNorm q.x k=stateNorm s.x k := by
  let J := (stdOrthonormalBasis ℝ
    (dataSpan (fun i : Fin (n+2) => s.x i) (fun i : Fin (n+2) => s.σ i))).repr.toLinearIsometry
  refine ⟨_,s.inSpan.map J,fun k hk => ?_⟩
  rw [stateNorm_map,stateNorm_inSpan s k hk]

variable [CompleteSpace E]

/-- Article: continuation of an admissible window preserves its positions, gradients and values.
The extension is one genuine normalized potential and one infinite actual free trajectory. -/
theorem exists_run_of_length_le (s : HSegment E A B β H n) (hn : n ≤ H+1) :
    ∃ r : Run E A B β,(∀ k,k ≤ n+1 → r.x k=s.x k) ∧
      ∀ i,1 ≤ i → i ≤ n → r.ψ (r.x i)=s.value i ∧ gradient r.ψ (r.x i)=s.σ i := by
  obtain ⟨q,hqx,hdata⟩ := (s.raw hn).exists_completion
  obtain ⟨ψ,hψ,hψdata⟩ := q.exists_potential
  let r : Run E A B β := ⟨ψ,hψ,freePosition (gradient ψ) A B β (s.x 0) (s.x 1),
    freePosition_recurrence (gradient ψ) A B β (s.x 0) (s.x 1)⟩
  have hx : q.x=s.x := hqx
  have hinterior (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ψ (s.x i)=s.value i ∧ gradient ψ (s.x i)=s.σ i := by
    have hh := hψdata i (by omega)
    rw [hx] at hh
    exact ⟨hh.1.trans (hdata i hi hin).2,hh.2.trans (hdata i hi hin).1⟩
  have hp (k : ℕ) (hk : k ≤ n) :
      freePair (gradient ψ) A B β (s.x 0) (s.x 1) k=(s.x k,s.x (k+1)) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [freePair,ih (by omega)]
      dsimp
      rw [(hinterior (k+1) (by omega) (by omega)).2,← s.recurrence k (by omega)]
  have hpos (k : ℕ) (hk : k ≤ n+1) : r.x k=s.x k := by
    cases k with
    | zero => rfl
    | succ k =>
      change (freePair (gradient ψ) A B β (s.x 0) (s.x 1) (k+1)).1=s.x (k+1)
      rw [freePair,hp k (by omega)]
  exact ⟨r,hpos,fun i hi hin => by rw [hpos i (by omega)]; exact hinterior i hi hin⟩

end HSegment
end
end polyak.Growth
