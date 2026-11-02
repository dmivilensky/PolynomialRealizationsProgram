import jacobi.Jacobi.Interpolation
import jacobi.Jacobi.ZerosGeometry

/-!
Article: jacobi, Proposition B.1.
One pair of positive parameter-dependent constants and one degree
threshold give the printed angular expansion, full corrected-node error,
endpoint and gap geometry, and interpolation estimate. Every quantity
is the genuine original polynomial zero or the literal source model.
Natural indices start at zero. The angular coordinate in (d) is the
physical inverse-cosine branch [0,pi], implicit in the source.
Use: converts the ordered gap theorem into the arbitrary-pair formulation of Proposition B.1 (c).
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter
open scoped Topology

/-- The source pair-index weight is symmetric in its two original indices.
Use: converts the ordered gap theorem into the arbitrary-pair formulation of Proposition B.1 (c).
Article: jacobi, Proposition B.1.
Proof: the two literal minimum arguments are symmetric natural-index sums. -/
theorem pairIndex_comm (n k l : ℕ) : pairIndex n k l=pairIndex n l k := by
  dsimp [pairIndex]
  congr 1 <;> omega

/-- The complete original zero proposition holds with one common pair of constants and one common degree threshold, for the full alpha,beta>-1 range.
Use: supplies all zero and interpolation estimates for the finite support-chain and persymmetric-limit proofs.
Article: jacobi, Proposition B.1.
Proof: combine the unconditional angular, corrected-node, geometric and
interpolation theorems. Decrease all lower constants to their minimum,
increase all upper constants to a common maximum, and intersect their
eventual degree ranges. Symmetry turns ordered gaps into arbitrary-pair
gaps. No asymptotic estimate or source conclusion is assumed. -/
theorem zeros_estimates {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∃ n0 : ℕ,∀ n≥n0,0<n ∧ 0<frequency a b n ∧
      (∀ k,2*k<n →
        |finiteAngleAt a b ha hb n k-modelAngle a b n k-
          (endpointCorrection a*(cos (modelAngle a b n k/2)/sin (modelAngle a b n k/2))-
            endpointCorrection b*(sin (modelAngle a b n k/2)/cos (modelAngle a b n k/2)))/(4*(frequency a b n)^2)|≤
          C*(1/(frequency a b n*(k+1:ℝ)^3)+1/(frequency a b n)^3)) ∧
      (∀ i : Fin n,|(nodes a b ha hb n).value i-modelNode a b n i.val|≤
        C*(1/((frequency a b n)^2*(edgeIndex n i.val:ℝ)^2)+(edgeIndex n i.val:ℝ)/(frequency a b n)^4)) ∧
      (∀ i : Fin n,c*(edgeIndex n i.val:ℝ)/frequency a b n≤min (angle a b ha hb i) (Real.pi-angle a b ha hb i) ∧
        min (angle a b ha hb i) (Real.pi-angle a b ha hb i)≤C*(edgeIndex n i.val:ℝ)/frequency a b n) ∧
      (∀ k : ℕ,∀ hk : k+1<n,c/frequency a b n≤
        angle a b ha hb (⟨k+1,hk⟩ : Fin n)-angle a b ha hb (⟨k,by omega⟩ : Fin n)) ∧
      (∀ i j : Fin n,c*|(i.val:ℝ)-j.val| *(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2≤
        |(nodes a b ha hb n).value i-(nodes a b ha hb n).value j|) ∧
      (∀ i j : Fin n,c*|(i.val:ℝ)-j.val| *(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2≤
        |modelNode a b n i.val-modelNode a b n j.val|) ∧
      (∀ i : Fin n,∀ theta : ℝ,theta ∈ Icc 0 Real.pi →
        modelScale a b n*cos theta+modelShift a b n ∈
          uIcc (modelNode a b n i.val) ((nodes a b ha hb n).value i) →
        c*(edgeIndex n i.val:ℝ)/(n:ℝ)≤sin theta ∧ sin theta≤C*(edgeIndex n i.val:ℝ)/(n:ℝ)) := by
  -- The component theorems concern the genuine source objects and discharge all phase, ODE, small-index and interpolation premises.
  obtain ⟨Ca,hCa,hA⟩ := zeros_angular_expansion ha hb
  obtain ⟨Cb,hCb,hB⟩ := zeros_node_error ha hb
  obtain ⟨cg,Cg,hcg,hCg,ng,hG⟩ := zeros_geometry ha hb
  obtain ⟨ci,Ci,hci,hCi,hI⟩ := zeros_interpolation ha hb
  let c := min cg ci
  let C := max Ca (max Cb (max Cg Ci))
  have hc : 0<c := lt_min hcg hci
  have hC : 0<C := lt_of_lt_of_le hCa (le_max_left _ _)
  have hcg' : c≤cg := min_le_left _ _
  have hci' : c≤ci := min_le_right _ _
  have hCa' : Ca≤C := le_max_left _ _
  have hCb' : Cb≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hCg' : Cg≤C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCi' : Ci≤C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨c,C,hc,hC,?_⟩
  apply eventually_atTop.mp
  filter_upwards [hA,hB,hI,eventually_ge_atTop ng] with n hAn hBn hIn hng
  obtain ⟨hN,hends,hgaps,hactual,hmodel⟩ := hG n hng
  refine ⟨hIn.1,hN,?_,?_,?_,?_,?_,?_,?_⟩
  · intro k hk
    exact (hAn.2 k hk).trans (mul_le_mul_of_nonneg_right hCa' (by positivity))
  · intro i
    exact (hBn.2 i).trans (mul_le_mul_of_nonneg_right hCb' (by positivity))
  · intro i
    exact ⟨(by calc
      _ ≤ cg*(edgeIndex n i.val:ℝ)/frequency a b n := by gcongr
      _ ≤ _ := (hends i).1), (by calc
      _ ≤ Cg*(edgeIndex n i.val:ℝ)/frequency a b n := (hends i).2
      _ ≤ _ := by gcongr)⟩
  · intro k hk
    exact (div_le_div_of_nonneg_right hcg' hN.le).trans (hgaps k hk)
  · have hpair : ∀ (v : Fin n → ℝ),
        (∀ i j : Fin n,i≤ j → cg*((j.val-i.val:ℕ):ℝ)*(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2≤|v i-v j|) →
        ∀ i j : Fin n,c*|(i.val:ℝ)-j.val| *(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2≤|v i-v j| := by
      intro v hv
      have hordered : ∀ i j : Fin n,i≤ j →
          c*|(i.val:ℝ)-j.val| *(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2≤|v i-v j| := by
        intro i j hij
        rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (show (i.val:ℝ)≤ j.val by exact_mod_cast hij)),← Nat.cast_sub (show i.val≤ j.val from hij)]
        exact (by calc
          _ ≤ cg*((j.val-i.val:ℕ):ℝ)*(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2 := by gcongr
          _ ≤ _ := hv i j hij)
      intro i j
      rcases le_total i j with hij | hji
      · exact hordered i j hij
      · simpa only [abs_sub_comm,pairIndex_comm] using hordered j i hji
    exact hpair _ hactual
  · -- Model gaps use the same pair symmetry and the same common lower constant.
    intro i j
    rcases le_total i j with hij | hji
    · rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (show (i.val:ℝ)≤ j.val by exact_mod_cast hij)),← Nat.cast_sub (show i.val≤ j.val from hij)]
      exact (by calc
        _ ≤ cg*((j.val-i.val:ℕ):ℝ)*(pairIndex n i.val j.val:ℝ)/(frequency a b n)^2 := by gcongr
        _ ≤ _ := hmodel i j hij)
    · rw [abs_of_nonneg (sub_nonneg.mpr (show (j.val:ℝ)≤ i.val by exact_mod_cast hji)),← Nat.cast_sub (show j.val≤ i.val from hji),pairIndex_comm n i.val j.val,abs_sub_comm (modelNode a b n i.val)]
      exact (by calc
        _ ≤ cg*((i.val-j.val:ℕ):ℝ)*(pairIndex n j.val i.val:ℝ)/(frequency a b n)^2 := by gcongr
        _ ≤ _ := hmodel j i hji)
  · intro i theta htheta hinterp
    have h := hIn.2 i theta htheta hinterp
    have hnR : (0:ℝ)≤n := Nat.cast_nonneg _
    exact ⟨(div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hci' (Nat.cast_nonneg _)) hnR).trans h.1,
      h.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCi' (Nat.cast_nonneg _)) hnR)⟩

end
end jacobi.Jacobi
