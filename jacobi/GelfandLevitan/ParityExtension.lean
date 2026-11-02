import jacobi.GelfandLevitan.TransformedBases

/-!
Article: jacobi, Proposition C.2.
The actual even and odd extensions of half-supported L2 vectors are
orthogonal after the original sqrt(2) normalization. Their coefficients
are the genuine half projections of the even and odd parts of the input.
This assembles the two proved transformed bases into the full system.
Use: fullTransformedVector joins the actual two transformed bases into the full original v_k system with its printed normalization.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The normalized physical parity extension of a genuine half-interval vector.
Use: fullTransformedVector joins the actual two transformed bases into the full original v_k system with its printed normalization.
Article: jacobi, Proposition C.2.
-/
def normalizedParityExtension (p : Fin 2) (v : halfSubspace) : Space :=
  (Real.sqrt 2)⁻¹ • halfParityExtension p v

/-- The genuine parity extensions have the exact original inner product factor.
Use: normalizedParityExtension_inner proves both the normalization within each class and orthogonality between the two classes in the full target basis.
Article: jacobi, Proposition C.2.
Proof: expand the two reflected sums. Disjoint half supports remove the cross terms, and the true reflection unitary preserves the remaining inner product. -/
theorem halfParityExtension_inner (p q : Fin 2) (v w : halfSubspace) :
    inner ℝ (halfParityExtension p v) (halfParityExtension q w)=
      (1+(-1:ℝ)^(p:ℕ)*(-1:ℝ)^(q:ℕ))*inner ℝ v w := by
  -- All reflections are the actual measure-preserving physical reflection, so no spatial symmetry assumption is needed on a half input.
  rw [halfParityExtension,halfParityExtension,inner_add_left,inner_add_right,inner_add_right,
    real_inner_smul_right,real_inner_smul_left,real_inner_smul_left,real_inner_smul_right,
    half_inner_reflection,reflectionUnitary_inner,
    half_inner_reflection,reflectionUnitary.inner_map_map]
  change inner ℝ (v:Space) (w:Space)+(-1:ℝ)^(q:ℕ)*0+
    ((-1:ℝ)^(p:ℕ)*0+(-1:ℝ)^(p:ℕ)*((-1:ℝ)^(q:ℕ)*inner ℝ (v:Space) (w:Space)))=
    (1+(-1:ℝ)^(p:ℕ)*(-1:ℝ)^(q:ℕ))*inner ℝ (v:Space) (w:Space)
  ring

/-- Normalized physical parity extension preserves inner products within a class and makes opposite classes orthogonal.
Use: fullTransformedVector_orthonormal verifies the actual full target system before its complete Hilbert basis is constructed.
Article: jacobi, Proposition C.2.
Proof: the proved extension pairing is multiplied by 1/2 from the two genuine sqrt(2) factors; the two real parity signs are either equal or opposite. -/
theorem normalizedParityExtension_inner (p q : Fin 2) (v w : halfSubspace) :
    inner ℝ (normalizedParityExtension p v) (normalizedParityExtension q w)=
      if p=q then inner ℝ v w else 0 := by
  classical
  rw [normalizedParityExtension,normalizedParityExtension,real_inner_smul_left,
    real_inner_smul_right,halfParityExtension_inner]
  fin_cases p <;> fin_cases q <;> norm_num <;> field_simp <;>
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

/-- The normalized extension has precisely the chosen genuine reflection sign.
Use: the full target basis and spectral operator commute with the original midpoint reflection.
Article: jacobi, Proposition C.2.
Proof: reflect the actual sum, use involutivity, and compare the two possible parity signs. -/
theorem normalizedParityExtension_reflection (p : Fin 2) (v : halfSubspace) :
    reflectionUnitary (normalizedParityExtension p v)=
      (-1:ℝ)^(p:ℕ) • normalizedParityExtension p v := by
  rw [normalizedParityExtension,map_smul,halfParityExtension,map_add,map_smul,
    reflectionUnitary_involutive]
  fin_cases p <;> norm_num <;> module

/-- The actual half-interval vector of parity coefficients of a full physical L2 input.
Use: fullTransformedVector_total reduces completeness of the reflected full system to the independently proved completeness of each actual half basis.
Article: jacobi, Proposition C.2.
-/
def parityRestriction (p : Fin 2) (v : Space) : halfSubspace :=
  halfSubspace.orthogonalProjectionOnto v+
    (-1:ℝ)^(p:ℕ) • halfSubspace.orthogonalProjectionOnto (reflectionUnitary v)

/-- The full pairing with a genuine normalized reflected wave is its actual half pairing with the corresponding restricted parity part.
Use: fullTransformedVector_total applies half-basis completeness without changing the physical measure or supplying a full completeness premise.
Article: jacobi, Proposition C.2.
Proof: move the true unitary reflection between the two inner-product slots and insert the genuine orthogonal half projection, which fixes every half-supported test vector. -/
theorem normalizedParityExtension_pairing (p : Fin 2) (u : halfSubspace) (v : Space) :
    inner ℝ (normalizedParityExtension p u) v=
      (Real.sqrt 2)⁻¹*inner ℝ u (parityRestriction p v) := by
  rw [normalizedParityExtension,real_inner_smul_left,halfParityExtension,inner_add_left,
    real_inner_smul_left,reflectionUnitary_inner,parityRestriction,inner_add_right,
    real_inner_smul_right u (halfSubspace.orthogonalProjectionOnto (reflectionUnitary v)) ((-1:ℝ)^(p:ℕ)),
    halfSubspace.inner_orthogonalProjectionOnto_eq_of_mem_left,
    halfSubspace.inner_orthogonalProjectionOnto_eq_of_mem_left]

/-- Both genuine restricted parity parts vanish only for the zero full input.
Use: fullTransformedVector_total recovers a full vector after both actual half bases annihilate its restricted parity parts.
Article: jacobi, Proposition C.2.
Proof: adding and subtracting the two parity conditions makes both genuine half projections zero; the actual reflected projection partition then makes the original full input zero. -/
theorem parityRestriction_total (v : Space) (h0 : parityRestriction 0 v=0)
    (h1 : parityRestriction 1 v=0) : v=0 := by
  -- The partition is an actual L2 identity, so the single null midpoint creates no additional condition.
  simp only [parityRestriction,Fin.val_zero,Fin.val_one,pow_zero,pow_one,one_smul,neg_smul] at h0 h1
  have hP : halfSubspace.orthogonalProjectionOnto v=0 := by
    have h : (2:ℝ) • halfSubspace.orthogonalProjectionOnto v=0 := by
      calc
        _ = (halfSubspace.orthogonalProjectionOnto v+
            halfSubspace.orthogonalProjectionOnto (reflectionUnitary v))+
          (halfSubspace.orthogonalProjectionOnto v-
            halfSubspace.orthogonalProjectionOnto (reflectionUnitary v)) := by module
        _ = 0 := by rw [h0,sub_eq_add_neg,h1,zero_add]
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have hR : halfSubspace.orthogonalProjectionOnto (reflectionUnitary v)=0 := by
    simpa only [hP,zero_add] using h0
  have h := fullHalfProjection_partition v
  change (halfSubspace.orthogonalProjectionOnto v:Space)+
    reflectionUnitary (halfSubspace.orthogonalProjectionOnto (reflectionUnitary v):Space)=v at h
  simpa only [hP,hR,ZeroMemClass.coe_zero,map_zero,add_zero] using h.symm

end
end jacobi.GelfandLevitan
