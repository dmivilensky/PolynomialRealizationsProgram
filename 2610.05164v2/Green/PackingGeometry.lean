import «2610.05164v2».Green.Exponential
import «2610.05164v2».Green.LiftContractivity

/-!
Article: 2610.05164v2, Theorem 2.3.
The space between neighboring even sites accommodates length 1/d_i.
Use: `«2610.05164v2».Jacobi.lift_interval_room` feeds `«2610.05164v2».Jacobi.intervalRight_le_even`
(interval Right le even).
Proof chain: `«2610.05164v2».Packing.exists_representation` — 2610.05164v2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
-/
namespace «2610.05164v2».Geometry
noncomputable section
open Real

/--
The stated quantitative bound `1/(2*t+1) ≤ (1/2:ℝ)*log (1+1/t)`.

Use: `«2610.05164v2».Jacobi.lift_interval_room` uses this bound to establish the stated
quantitative bound `1/J.green i i ≤ J.lift.position (by omega) ⟨2*i.val+1,by omega⟩ -
J.lift.position (by omega) ⟨2*i.val-1,by omega⟩`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem spacing_lower_bound (t : ℝ) (ht : 0 < t) :
    1/(2*t+1) ≤ (1/2:ℝ)*log (1+1/t) := by
  have he := le_log_one_add_of_nonneg (one_div_pos.mpr ht).le
  have hc : 2*(1/t)/(1/t+2) = 2/(2*t+1) := by field_simp; ring
  rw [hc] at he
  rw [div_eq_mul_inv] at he
  rw [one_div]
  linarith

/--
The stated quantitative bound `4/(a+b) ≤ 1/a+1/b`.

Use: `«2610.05164v2».Jacobi.lift_interval_room` uses this bound to establish the stated
quantitative bound `1/J.green i i ≤ J.lift.position (by omega) ⟨2*i.val+1,by omega⟩ -
J.lift.position (by omega) ⟨2*i.val-1,by omega⟩`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem reciprocal_sum (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    4/(a+b) ≤ 1/a+1/b := by
  apply (div_le_iff₀ (add_pos ha hb)).mpr
  field_simp
  nlinarith [sq_nonneg (a-b)]

end
end «2610.05164v2».Geometry

namespace «2610.05164v2».Jacobi
noncomputable section
open Real Matrix
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} (J : Jacobi N)

/--
Exact identity `J.incomingFlow j = J.edgeFlow i`.

Use: `«2610.05164v2».Jacobi.lift_interval_room` rewrites with this identity to establish the
stated quantitative bound `1/J.green i i ≤ J.lift.position (by omega) ⟨2*i.val+1,by omega⟩ -
J.lift.position (by omega) ⟨2*i.val-1,by omega⟩`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem incomingFlow_eq_edgeFlow (i j : Fin N) (hij : i.val+1 = j.val) :
    J.incomingFlow j = J.edgeFlow i := by
  have hi : 0 < j.val := by omega
  have hn : i.val+1 < N := by omega
  have hp : (⟨j.val-1,by omega⟩ : Fin N) = i := Fin.ext (by change j.val-1 = i.val; omega)
  have hs : (⟨i.val+1,hn⟩ : Fin N) = j := Fin.ext hij
  rw [incomingFlow, edgeFlow, dite_eq_left hi, dite_eq_left hn, hp, hs, hij]

/--
Defines `representationPoint` of type `(hN : 0 < N) (i : Fin N)` by `J.lift.position (by omega)
(Centering.interleave N (Sum.inl i))`.

Use: `«2610.05164v2».Jacobi.green_representation` uses this definition to establish exact
identity `J.green i j = sqrt (J.green i i*J.green j j)* exp (-|J.representationPoint hN
i-J.representationPoint hN j|)`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.
-/
def representationPoint (hN : 0 < N) (i : Fin N) :=
  J.lift.position (by omega) (Centering.interleave N (Sum.inl i))

/--
The precise assertion is `StrictMono (J.representationPoint hN)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 2.3.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.pencils_of_contractive`,
`«2610.05164v2».Jacobi.lift_pencils`, `«2610.05164v2».Jacobi.lift_centered` with the arguments
shown in the proof.
-/
theorem representationPoint_strictMono (hN : 0 < N) (h : «2606.16671v2».opNorm J.matrix < 1)
    (hir : J.Irreducible) : StrictMono (J.representationPoint hN) := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.pencils_of_contractive`,
  -- `«2610.05164v2».Jacobi.lift_pencils`, `«2610.05164v2».Jacobi.lift_centered` with the
  -- arguments shown in the proof.
  obtain ⟨hm,hp⟩ := J.pencils_of_contractive h
  obtain ⟨hm',_⟩ := J.lift_pencils hp hm
  have hc := J.lift_centered hp hir
  intro i j hij
  apply J.lift.position_strictMono (by omega) hm' hc.2 hc.1
  change (Centering.interleave N (Sum.inl i)).val < (Centering.interleave N (Sum.inl j)).val
  simp only [Centering.interleave_left]
  exact Nat.mul_lt_mul_of_pos_left hij (by norm_num)

/--
The kernel representation in Proposition 1, for the original chain.

Exact identity `J.green i j = sqrt (J.green i i*J.green j j)* exp (-|J.representationPoint hN
i-J.representationPoint hN j|)`.

Use: `«2610.05164v2».Packing.Jacobi.atomicMatrix_eq_normalizedGreen` rewrites with this
identity to establish the identity `atomicMatrix (atomicWeight J) (J.representationPoint hN)
= J.normalizedGreen`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.pencils_of_contractive`,
`«2610.05164v2».Jacobi.lift_pencils`, `«2610.05164v2».Jacobi.lift_centered` with the arguments
shown in the proof.
-/
theorem green_representation (hN : 0 < N) (h : «2606.16671v2».opNorm J.matrix < 1)
    (hir : J.Irreducible) (i j : Fin N) :
    J.green i j = sqrt (J.green i i*J.green j j)*
      exp (-|J.representationPoint hN i-J.representationPoint hN j|) := by
  -- Use the identities/estimates `«2610.05164v2».Jacobi.pencils_of_contractive`,
  -- `«2610.05164v2».Jacobi.lift_pencils`, `«2610.05164v2».Jacobi.lift_centered` with the
  -- arguments shown in the proof.
  obtain ⟨hm,hp⟩ := J.pencils_of_contractive h
  obtain ⟨hm',_⟩ := J.lift_pencils hp hm
  have hc := J.lift_centered hp hir
  have he := J.lift.green_exponential (by omega) hm' hc.2 hc.1
    (Centering.interleave N (Sum.inl i)) (Centering.interleave N (Sum.inl j))
  rw [J.lift_green_odd hp hm, J.lift_green_odd hp hm, J.lift_green_odd hp hm] at he
  have hs : sqrt (2*J.green i i*(2*J.green j j)) = 2*sqrt (J.green i i*J.green j j) := by
    rw [show 2*J.green i i*(2*J.green j j) = (2:ℝ)^2*(J.green i i*J.green j j) by ring,
      sqrt_mul (by positivity), sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [hs] at he
  change 2*J.green i j = (2*sqrt (J.green i i*J.green j j))*
    exp (-|J.representationPoint hN i-J.representationPoint hN j|) at he
  linarith

/--
The space between neighboring even sites accommodates length 1/d_i.

The stated quantitative bound `1/J.green i i ≤ J.lift.position (by omega) ⟨2*i.val+1,by omega⟩
- J.lift.position (by omega) ⟨2*i.val-1,by omega⟩`.

Use: `«2610.05164v2».Jacobi.intervalRight_le_even` uses this bound to establish the stated
quantitative bound `J.intervalRight hN i ≤ J.lift.position (by omega) ⟨2*i.val+1,by omega⟩`.

Article: 2610.05164v2, Theorem 2.3 via `«2610.05164v2».Packing.exists_representation`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem lift_interval_room (hN : 0 < N) (h : «2606.16671v2».opNorm J.matrix < 1)
    (hir : J.Irreducible) (i : Fin N) (hi : 0 < i.val) (hin : i.val+1 < N) :
    1/J.green i i ≤ J.lift.position (by omega) ⟨2*i.val+1,by omega⟩ -
      J.lift.position (by omega) ⟨2*i.val-1,by omega⟩ := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  obtain ⟨hm,hp⟩ := J.pencils_of_contractive h
  obtain ⟨hm',_⟩ := J.lift_pencils hp hm
  have hc := J.lift_centered hp hir
  let l : Fin (2*N) := ⟨2*i.val-1,by omega⟩
  let m : Fin (2*N) := Centering.interleave N (Sum.inl i)
  let r : Fin (2*N) := ⟨2*i.val+1,by omega⟩
  have hlm : l.val+1 = m.val := by simp [l,m]; omega
  have hmr : m.val+1 = r.val := by simp [m,r]
  have htl := J.lift.edgeFlow_pos hm' hc.1 l (by dsimp [l]; omega)
  have htm := J.lift.edgeFlow_pos hm' hc.1 m (by simp [m]; omega)
  have hsl := J.lift.position_spacing (by omega) hm' hc.2 hc.1 l m hlm
  have hsm := J.lift.position_spacing (by omega) hm' hc.2 hc.1 m r hmr
  have hbl := Geometry.spacing_lower_bound _ htl
  have hbm := Geometry.spacing_lower_bound _ htm
  have hd := J.lift.centered_green_diagonal hm' hc.2 m
  rw [J.lift.incomingFlow_eq_edgeFlow l m hlm] at hd
  have hmass : J.lift.green m m = 2*J.green i i := J.lift_green_odd hp hm i i
  have hdpos : 0 < J.green i i := hm.inv.diag_pos
  have hs := Geometry.reciprocal_sum (2*J.lift.edgeFlow l+1) (2*J.lift.edgeFlow m+1)
    (by linarith) (by linarith)
  have he : 4/(2*J.lift.edgeFlow l+1+(2*J.lift.edgeFlow m+1)) = 1/J.green i i := by
    have hh : 2*J.lift.edgeFlow l+1+(2*J.lift.edgeFlow m+1) = 4*J.green i i := by
      linarith
    rw [hh]; field_simp
  rw [he] at hs
  change 1/J.green i i ≤ J.lift.position _ r-J.lift.position _ l
  linarith

end
end «2610.05164v2».Jacobi
