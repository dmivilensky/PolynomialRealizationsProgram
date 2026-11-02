import jacobi.Comparison.WeightRatio
import jacobi.Jacobi.Zeros
import jacobi.Reference.NormingBounds

/-!
Article: jacobi, Appendix C.4 (target/support weight ratios).
Every actual finite relative-gap factor has the quantitative logarithmic
majorant obtained from the proved original two-edge node errors and gap
lower bounds. The same exact original factors form relativeGapProduct;
no asymptotic comparison measure or separate gap hypothesis is introduced.
Use: relativeGapProduct_log_sum and comparisonGap_log_majorant use the actual real logarithm on its true positive original branch.
-/
namespace jacobi.Comparison
noncomputable section
open Real Finset Filter jacobi.Reference
open scoped Topology

/-- Every genuine off-diagonal target/support gap ratio is positive.
Use: relativeGapProduct_log_sum and comparisonGap_log_majorant use the actual real logarithm on its true positive original branch.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: both actual spectral node families are independently proved injective, so both original absolute gaps are positive. -/
theorem comparisonGap_pos (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ)
    (i j:Fin (n+1)) (hij:i≠j) :
    0<(|jacobi.Jacobi.modelNode a b (n+1) i.val- jacobi.Jacobi.modelNode a b (n+1) j.val|/
      |(jacobi.Jacobi.nodes a b ha hb (n+1)).value i-(jacobi.Jacobi.nodes a b ha hb (n+1)).value j|) := by
  apply div_pos <;> apply abs_pos.mpr <;> apply sub_ne_zero.mpr
  · exact fun he => hij ((jacobi.Support.correctedNodes_injective ha hb (by omega)) he)
  · exact fun he => hij ((jacobi.Jacobi.nodes a b ha hb (n+1)).strictAnti.injective he)

/-- The logarithm of the actual relative product is the exact finite sum of the original individual gap logarithms.
Use: the quantitative whole-product logarithm estimate is obtained by summing comparisonGap_log_majorant over precisely this original omitted-diagonal set.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: each original factor has the independently proved strict positive value, so the community finite logarithm-product identity applies. -/
theorem relativeGapProduct_log_sum (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i:Fin (n+1)) :
    log (relativeGapProduct a b ha hb n i)=∑j∈univ.erase i,
      log (|jacobi.Jacobi.modelNode a b (n+1) i.val- jacobi.Jacobi.modelNode a b (n+1) j.val|/
        |(jacobi.Jacobi.nodes a b ha hb (n+1)).value i-(jacobi.Jacobi.nodes a b ha hb (n+1)).value j|) :=
  log_prod (fun j hj => (comparisonGap_pos a b ha hb n i j (mem_erase.mp hj).1.symm).ne')

/-- Every actual original finite gap ratio has its full two-edge quantitative logarithm majorant, uniformly over both original spectral indices.
Use: summing this actual factor estimate gives the full finite relative-product bound in Appendix C.4; its summable first part controls the spectral edges and its harmonic second part controls the growing bulk.
Article: jacobi, Appendix C.4 (target/support weight ratios).
Proof: the complete proved Proposition B.1 supplies one common positive lower gap and the two actual node-error bounds. Absolute differences of absolute gaps are at most the sum of the two original node errors. Apply the already proved global positive-gap logarithm inequality and cancel the same positive frequency square to obtain the printed two-part row majorant. -/
theorem comparisonGap_log_majorant {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀i j:Fin (n+1),i≠j→
      |log (|jacobi.Jacobi.modelNode a b (n+1) i.val- jacobi.Jacobi.modelNode a b (n+1) j.val|/
        |(jacobi.Jacobi.nodes a b ha hb (n+1)).value i-(jacobi.Jacobi.nodes a b ha hb (n+1)).value j|)|≤
      C*((1/(jacobi.Jacobi.edgeIndex (n+1) i.val:ℝ)^2+1/(jacobi.Jacobi.edgeIndex (n+1) j.val:ℝ)^2)/
          (|(i.val:ℝ)-j.val| *(jacobi.Jacobi.pairIndex (n+1) i.val j.val:ℝ))+
        ((jacobi.Jacobi.edgeIndex (n+1) i.val:ℝ)+(jacobi.Jacobi.edgeIndex (n+1) j.val:ℝ))/
          ((jacobi.Jacobi.frequency a b (n+1))^2*|(i.val:ℝ)-j.val| *(jacobi.Jacobi.pairIndex (n+1) i.val j.val:ℝ))) := by
  -- Both gap and displacement inputs refer to the same genuine sorted original nodes.
  obtain ⟨c,C,hc,hC,n₀,hzeros⟩ := jacobi.Jacobi.zeros_estimates ha hb
  refine ⟨C/c,div_pos hC hc,?_⟩
  filter_upwards [eventually_ge_atTop n₀] with n hn
  intro i j hij
  obtain ⟨_,hN,_,he,_,_,hz,hm,_⟩ := hzeros (n+1) (by omega)
  let F := jacobi.Jacobi.frequency a b (n+1)
  let di : ℝ := jacobi.Jacobi.edgeIndex (n+1) i.val
  let dj : ℝ := jacobi.Jacobi.edgeIndex (n+1) j.val
  let m : ℝ := jacobi.Jacobi.pairIndex (n+1) i.val j.val
  let d : ℝ := |(i.val:ℝ)-j.val|
  have hdi : 0<di := by
    dsimp [di]
    exact_mod_cast (show 0< jacobi.Jacobi.edgeIndex (n+1) i.val by dsimp [jacobi.Jacobi.edgeIndex]; omega)
  have hdj : 0<dj := by
    dsimp [dj]
    exact_mod_cast (show 0< jacobi.Jacobi.edgeIndex (n+1) j.val by dsimp [jacobi.Jacobi.edgeIndex]; omega)
  have hmpos : 0<m := by
    dsimp [m]
    exact_mod_cast (show 0< jacobi.Jacobi.pairIndex (n+1) i.val j.val by dsimp [jacobi.Jacobi.pairIndex]; omega)
  have hd : 0<d := by
    apply abs_pos.mpr
    apply sub_ne_zero.mpr
    intro heq
    exact hij (Fin.ext (by exact_mod_cast heq))
  have hgap : 0<c*d*m/F^2 := div_pos (mul_pos (mul_pos hc hd) hmpos) (sq_pos_of_pos hN)
  have herror :
      abs (|jacobi.Jacobi.modelNode a b (n+1) i.val- jacobi.Jacobi.modelNode a b (n+1) j.val|-
        |(jacobi.Jacobi.nodes a b ha hb (n+1)).value i-(jacobi.Jacobi.nodes a b ha hb (n+1)).value j|)≤
      C*((1/(F^2*di^2)+di/F^4)+(1/(F^2*dj^2)+dj/F^4)) := by
    calc
      _ ≤ |(jacobi.Jacobi.modelNode a b (n+1) i.val- jacobi.Jacobi.modelNode a b (n+1) j.val)-
          ((jacobi.Jacobi.nodes a b ha hb (n+1)).value i-(jacobi.Jacobi.nodes a b ha hb (n+1)).value j)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |((jacobi.Jacobi.nodes a b ha hb (n+1)).value j- jacobi.Jacobi.modelNode a b (n+1) j.val)-
          ((jacobi.Jacobi.nodes a b ha hb (n+1)).value i- jacobi.Jacobi.modelNode a b (n+1) i.val)| := by congr 1; ring
      _ ≤ |(jacobi.Jacobi.nodes a b ha hb (n+1)).value j- jacobi.Jacobi.modelNode a b (n+1) j.val|+
          |(jacobi.Jacobi.nodes a b ha hb (n+1)).value i- jacobi.Jacobi.modelNode a b (n+1) i.val| := abs_sub _ _
      _ ≤ C*(1/(F^2*dj^2)+dj/F^4)+C*(1/(F^2*di^2)+di/F^4) := add_le_add (he j) (he i)
      _ = _ := by ring
  have h := log_gap_ratio_le hgap (hm i j) (hz i j) herror
  have hF : F≠0 := hN.ne'
  have hformula : C*((1/(F^2*di^2)+di/F^4)+(1/(F^2*dj^2)+dj/F^4))/(c*d*m/F^2)=
      (C/c)*((1/di^2+1/dj^2)/(d*m)+(di+dj)/(F^2*d*m)) := by
    field_simp [hc.ne',hF,hdi.ne',hdj.ne',hd.ne',hmpos.ne']
    ring
  exact h.trans_eq hformula

end
end jacobi.Comparison
