import polyak.Numerics.KernelDecide
import polyak.Boundary.P2.Chebyshev

/-! Article: exact source moment expansions for all raw lags 1 through 9. -/
namespace polyak.Boundary.P2
noncomputable section
open Polynomial
/-- Article: exact quadratic-moment source of raw lower1. -/
theorem lower1_source (z : ℝ) : reducedSlack z 1 (-1 : ℝ)=((moment z 3)+(d z)+((moment z 0)*((G z)+(-2*(u z))+(-1*(G z)*((u z))^2)))+((moment z 1)*(-1+((u z))^2))+((moment z 2)*((-1*(G z))+(2*(u z))))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 1 (G z))-Chebyshev.T ℝ 1)+
        C ((-1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 0=((C (1))*X^3+(C (((-1*(G z))+(2*(u z)))))*X^2+(C ((-1+((u z))^2)))*X^1+(C (((G z)+(-2*(u z))+(-1*(G z)*((u z))^2))))*X^0) := by
    rw [Tpoly1,Upoly0]
    norm_num [Spectral.chebT,Tpoly1,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly0]
  ring

/-- Article: exact quadratic-moment source of raw upper1. -/
theorem upper1_source (z : ℝ) : reducedSlack z 1 (1 : ℝ)=((moment z 3)+(-1*(d z))+((moment z 0)*((G z)+(2*(u z))+(-1*(G z)*((u z))^2)))+((moment z 1)*(-1+((u z))^2))+((moment z 2)*((-1*(G z))+(-2*(u z))))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 1 (G z))-Chebyshev.T ℝ 1)+
        C ((1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 0=((C (1))*X^3+(C (((-1*(G z))+(-2*(u z)))))*X^2+(C ((-1+((u z))^2)))*X^1+(C (((G z)+(2*(u z))+(-1*(G z)*((u z))^2))))*X^0) := by
    rw [Tpoly1,Upoly0]
    norm_num [Spectral.chebT,Tpoly1,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly0]
  ring

/-- Article: exact quadratic-moment source of raw lower2. -/
theorem lower2_source (z : ℝ) : reducedSlack z 2 (-1 : ℝ)=((2*(moment z 4))+((moment z 0)*((2*((G z))^2)+(-2*((G z))^2*((u z))^2)))+((moment z 2)*(-2+(-2*((G z))^2)+(2*((u z))^2)))+(-4*(moment z 1)*(u z))+(2*(G z)*(d z))+(4*(moment z 3)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 2 (G z))-Chebyshev.T ℝ 2)+
        C ((-1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 1=((C (2))*X^4+(C ((4*(u z))))*X^3+(C ((-2+(-2*((G z))^2)+(2*((u z))^2))))*X^2+(C ((-4*(u z))))*X^1+(C (((2*((G z))^2)+(-2*((G z))^2*((u z))^2))))*X^0) := by
    rw [Tpoly2,Upoly1]
    norm_num [Spectral.chebT,Tpoly2,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly1]
  ring

/-- Article: exact quadratic-moment source of raw upper2. -/
theorem upper2_source (z : ℝ) : reducedSlack z 2 (1 : ℝ)=((2*(moment z 4))+((moment z 0)*((2*((G z))^2)+(-2*((G z))^2*((u z))^2)))+((moment z 2)*(-2+(-2*((G z))^2)+(2*((u z))^2)))+(-4*(moment z 3)*(u z))+(-2*(G z)*(d z))+(4*(moment z 1)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 2 (G z))-Chebyshev.T ℝ 2)+
        C ((1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 1=((C (2))*X^4+(C ((-4*(u z))))*X^3+(C ((-2+(-2*((G z))^2)+(2*((u z))^2))))*X^2+(C ((4*(u z))))*X^1+(C (((2*((G z))^2)+(-2*((G z))^2*((u z))^2))))*X^0) := by
    rw [Tpoly2,Upoly1]
    norm_num [Spectral.chebT,Tpoly2,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly1]
  ring

/-- Article: exact quadratic-moment source of raw lower3. -/
theorem lower3_source (z : ℝ) : reducedSlack z 3 (-1 : ℝ)=((4*(moment z 5))+((moment z 0)*((-3*(G z))+(2*(u z))+(4*((G z))^3)+(-4*((G z))^3*((u z))^2)+(3*(G z)*((u z))^2)))+((moment z 1)*(3+(-3*((u z))^2)))+((moment z 2)*((-10*(u z))+(-4*((G z))^3)+(3*(G z))))+((moment z 3)*(-7+(4*((u z))^2)))+((d z)*(-1+(4*((G z))^2)))+(8*(moment z 4)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 3 (G z))-Chebyshev.T ℝ 3)+
        C ((-1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 2=((C (4))*X^5+(C ((8*(u z))))*X^4+(C ((-7+(4*((u z))^2))))*X^3+(C (((-10*(u z))+(-4*((G z))^3)+(3*(G z)))))*X^2+(C ((3+(-3*((u z))^2))))*X^1+(C (((-3*(G z))+(2*(u z))+(4*((G z))^3)+(-4*((G z))^3*((u z))^2)+(3*(G z)*((u z))^2))))*X^0) := by
    rw [Tpoly3,Upoly2]
    norm_num [Spectral.chebT,Tpoly3,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly2]
  ring

/-- Article: exact quadratic-moment source of raw upper3. -/
theorem upper3_source (z : ℝ) : reducedSlack z 3 (1 : ℝ)=((4*(moment z 5))+((moment z 0)*((-3*(G z))+(-2*(u z))+(4*((G z))^3)+(-4*((G z))^3*((u z))^2)+(3*(G z)*((u z))^2)))+((moment z 1)*(3+(-3*((u z))^2)))+((moment z 2)*((-4*((G z))^3)+(3*(G z))+(10*(u z))))+((moment z 3)*(-7+(4*((u z))^2)))+(-1*(d z)*(-1+(4*((G z))^2)))+(-8*(moment z 4)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 3 (G z))-Chebyshev.T ℝ 3)+
        C ((1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 2=((C (4))*X^5+(C ((-8*(u z))))*X^4+(C ((-7+(4*((u z))^2))))*X^3+(C (((-4*((G z))^3)+(3*(G z))+(10*(u z)))))*X^2+(C ((3+(-3*((u z))^2))))*X^1+(C (((-3*(G z))+(-2*(u z))+(4*((G z))^3)+(-4*((G z))^3*((u z))^2)+(3*(G z)*((u z))^2))))*X^0) := by
    rw [Tpoly3,Upoly2]
    norm_num [Spectral.chebT,Tpoly3,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly2]
  ring

/-- Article: exact quadratic-moment source of raw lower4. -/
theorem lower4_source (z : ℝ) : reducedSlack z 4 (-1 : ℝ)=((8*(moment z 6))+((moment z 0)*((-8*((G z))^2)+(8*((G z))^4)+(-8*((G z))^4*((u z))^2)+(8*((G z))^2*((u z))^2)))+((moment z 2)*(8+(-8*((G z))^4)+(-8*((u z))^2)+(8*((G z))^2)))+((moment z 4)*(-16+(8*((u z))^2)))+((d z)*((-4*(G z))+(8*((G z))^3)))+(-24*(moment z 3)*(u z))+(8*(moment z 1)*(u z))+(16*(moment z 5)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 4 (G z))-Chebyshev.T ℝ 4)+
        C ((-1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 3=((C (8))*X^6+(C ((16*(u z))))*X^5+(C ((-16+(8*((u z))^2))))*X^4+(C ((-24*(u z))))*X^3+(C ((8+(-8*((G z))^4)+(-8*((u z))^2)+(8*((G z))^2))))*X^2+(C ((8*(u z))))*X^1+(C (((-8*((G z))^2)+(8*((G z))^4)+(-8*((G z))^4*((u z))^2)+(8*((G z))^2*((u z))^2))))*X^0) := by
    rw [Tpoly4,Upoly3]
    norm_num [Spectral.chebT,Tpoly4,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly3]
  ring

/-- Article: exact quadratic-moment source of raw upper4. -/
theorem upper4_source (z : ℝ) : reducedSlack z 4 (1 : ℝ)=((8*(moment z 6))+((moment z 0)*((-8*((G z))^2)+(8*((G z))^4)+(-8*((G z))^4*((u z))^2)+(8*((G z))^2*((u z))^2)))+((moment z 2)*(8+(-8*((G z))^4)+(-8*((u z))^2)+(8*((G z))^2)))+((moment z 4)*(-16+(8*((u z))^2)))+(-1*(d z)*((-4*(G z))+(8*((G z))^3)))+(-16*(moment z 5)*(u z))+(-8*(moment z 1)*(u z))+(24*(moment z 3)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 4 (G z))-Chebyshev.T ℝ 4)+
        C ((1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 3=((C (8))*X^6+(C ((-16*(u z))))*X^5+(C ((-16+(8*((u z))^2))))*X^4+(C ((24*(u z))))*X^3+(C ((8+(-8*((G z))^4)+(-8*((u z))^2)+(8*((G z))^2))))*X^2+(C ((-8*(u z))))*X^1+(C (((-8*((G z))^2)+(8*((G z))^4)+(-8*((G z))^4*((u z))^2)+(8*((G z))^2*((u z))^2))))*X^0) := by
    rw [Tpoly4,Upoly3]
    norm_num [Spectral.chebT,Tpoly4,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly3]
  ring

/-- Article: exact quadratic-moment source of raw lower5. -/
theorem lower5_source (z : ℝ) : reducedSlack z 5 (-1 : ℝ)=((16*(moment z 7))+((moment z 0)*((-20*((G z))^3)+(-2*(u z))+(5*(G z))+(16*((G z))^5)+(-16*((G z))^5*((u z))^2)+(-5*(G z)*((u z))^2)+(20*((G z))^3*((u z))^2)))+((moment z 1)*(-5+(5*((u z))^2)))+((moment z 2)*((-16*((G z))^5)+(-5*(G z))+(20*((G z))^3)+(26*(u z))))+((moment z 3)*(25+(-20*((u z))^2)))+((moment z 5)*(-36+(16*((u z))^2)))+((d z)*(1+(-12*((G z))^2)+(16*((G z))^4)))+(-56*(moment z 4)*(u z))+(32*(moment z 6)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 5 (G z))-Chebyshev.T ℝ 5)+
        C ((-1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 4=((C (16))*X^7+(C ((32*(u z))))*X^6+(C ((-36+(16*((u z))^2))))*X^5+(C ((-56*(u z))))*X^4+(C ((25+(-20*((u z))^2))))*X^3+(C (((-16*((G z))^5)+(-5*(G z))+(20*((G z))^3)+(26*(u z)))))*X^2+(C ((-5+(5*((u z))^2))))*X^1+(C (((-20*((G z))^3)+(-2*(u z))+(5*(G z))+(16*((G z))^5)+(-16*((G z))^5*((u z))^2)+(-5*(G z)*((u z))^2)+(20*((G z))^3*((u z))^2))))*X^0) := by
    rw [Tpoly5,Upoly4]
    norm_num [Spectral.chebT,Tpoly5,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly4]
  ring

/-- Article: exact quadratic-moment source of raw upper5. -/
theorem upper5_source (z : ℝ) : reducedSlack z 5 (1 : ℝ)=((16*(moment z 7))+((moment z 0)*((-20*((G z))^3)+(2*(u z))+(5*(G z))+(16*((G z))^5)+(-16*((G z))^5*((u z))^2)+(-5*(G z)*((u z))^2)+(20*((G z))^3*((u z))^2)))+((moment z 1)*(-5+(5*((u z))^2)))+((moment z 2)*((-26*(u z))+(-16*((G z))^5)+(-5*(G z))+(20*((G z))^3)))+((moment z 3)*(25+(-20*((u z))^2)))+((moment z 5)*(-36+(16*((u z))^2)))+(-1*(d z)*(1+(-12*((G z))^2)+(16*((G z))^4)))+(-32*(moment z 6)*(u z))+(56*(moment z 4)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 5 (G z))-Chebyshev.T ℝ 5)+
        C ((1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 4=((C (16))*X^7+(C ((-32*(u z))))*X^6+(C ((-36+(16*((u z))^2))))*X^5+(C ((56*(u z))))*X^4+(C ((25+(-20*((u z))^2))))*X^3+(C (((-26*(u z))+(-16*((G z))^5)+(-5*(G z))+(20*((G z))^3))))*X^2+(C ((-5+(5*((u z))^2))))*X^1+(C (((-20*((G z))^3)+(2*(u z))+(5*(G z))+(16*((G z))^5)+(-16*((G z))^5*((u z))^2)+(-5*(G z)*((u z))^2)+(20*((G z))^3*((u z))^2))))*X^0) := by
    rw [Tpoly5,Upoly4]
    norm_num [Spectral.chebT,Tpoly5,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly4]
  ring

/-- Article: exact quadratic-moment source of raw lower6. -/
theorem lower6_source (z : ℝ) : reducedSlack z 6 (-1 : ℝ)=((32*(moment z 8))+((moment z 0)*((-48*((G z))^4)+(18*((G z))^2)+(32*((G z))^6)+(-32*((G z))^6*((u z))^2)+(-18*((G z))^2*((u z))^2)+(48*((G z))^4*((u z))^2)))+((moment z 2)*(-18+(-32*((G z))^6)+(-18*((G z))^2)+(18*((u z))^2)+(48*((G z))^4)))+((moment z 4)*(66+(-48*((u z))^2)))+((moment z 6)*(-80+(32*((u z))^2)))+((d z)*((-32*((G z))^3)+(6*(G z))+(32*((G z))^5)))+(-128*(moment z 5)*(u z))+(-12*(moment z 1)*(u z))+(64*(moment z 7)*(u z))+(76*(moment z 3)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 6 (G z))-Chebyshev.T ℝ 6)+
        C ((-1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 5=((C (32))*X^8+(C ((64*(u z))))*X^7+(C ((-80+(32*((u z))^2))))*X^6+(C ((-128*(u z))))*X^5+(C ((66+(-48*((u z))^2))))*X^4+(C ((76*(u z))))*X^3+(C ((-18+(-32*((G z))^6)+(-18*((G z))^2)+(18*((u z))^2)+(48*((G z))^4))))*X^2+(C ((-12*(u z))))*X^1+(C (((-48*((G z))^4)+(18*((G z))^2)+(32*((G z))^6)+(-32*((G z))^6*((u z))^2)+(-18*((G z))^2*((u z))^2)+(48*((G z))^4*((u z))^2))))*X^0) := by
    rw [Tpoly6,Upoly5]
    norm_num [Spectral.chebT,Tpoly6,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly5]
  ring

/-- Article: exact quadratic-moment source of raw upper6. -/
theorem upper6_source (z : ℝ) : reducedSlack z 6 (1 : ℝ)=((32*(moment z 8))+((moment z 0)*((-48*((G z))^4)+(18*((G z))^2)+(32*((G z))^6)+(-32*((G z))^6*((u z))^2)+(-18*((G z))^2*((u z))^2)+(48*((G z))^4*((u z))^2)))+((moment z 2)*(-18+(-32*((G z))^6)+(-18*((G z))^2)+(18*((u z))^2)+(48*((G z))^4)))+((moment z 4)*(66+(-48*((u z))^2)))+((moment z 6)*(-80+(32*((u z))^2)))+(-1*(d z)*((-32*((G z))^3)+(6*(G z))+(32*((G z))^5)))+(-76*(moment z 3)*(u z))+(-64*(moment z 7)*(u z))+(12*(moment z 1)*(u z))+(128*(moment z 5)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 6 (G z))-Chebyshev.T ℝ 6)+
        C ((1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 5=((C (32))*X^8+(C ((-64*(u z))))*X^7+(C ((-80+(32*((u z))^2))))*X^6+(C ((128*(u z))))*X^5+(C ((66+(-48*((u z))^2))))*X^4+(C ((-76*(u z))))*X^3+(C ((-18+(-32*((G z))^6)+(-18*((G z))^2)+(18*((u z))^2)+(48*((G z))^4))))*X^2+(C ((12*(u z))))*X^1+(C (((-48*((G z))^4)+(18*((G z))^2)+(32*((G z))^6)+(-32*((G z))^6*((u z))^2)+(-18*((G z))^2*((u z))^2)+(48*((G z))^4*((u z))^2))))*X^0) := by
    rw [Tpoly6,Upoly5]
    norm_num [Spectral.chebT,Tpoly6,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly5]
  ring

/-- Article: exact quadratic-moment source of raw lower7. -/
theorem lower7_source (z : ℝ) : reducedSlack z 7 (-1 : ℝ)=((64*(moment z 9))+((moment z 0)*((-112*((G z))^5)+(-7*(G z))+(2*(u z))+(56*((G z))^3)+(64*((G z))^7)+(-64*((G z))^7*((u z))^2)+(-56*((G z))^3*((u z))^2)+(7*(G z)*((u z))^2)+(112*((G z))^5*((u z))^2)))+((moment z 1)*(7+(-7*((u z))^2)))+((moment z 2)*((-64*((G z))^7)+(-56*((G z))^3)+(-50*(u z))+(7*(G z))+(112*((G z))^5)))+((moment z 3)*(-63+(56*((u z))^2)))+((moment z 5)*(168+(-112*((u z))^2)))+((moment z 7)*(-176+(64*((u z))^2)))+((d z)*(-1+(-80*((G z))^4)+(24*((G z))^2)+(64*((G z))^6)))+(-288*(moment z 6)*(u z))+(128*(moment z 8)*(u z))+(208*(moment z 4)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 7 (G z))-Chebyshev.T ℝ 7)+
        C ((-1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 6=((C (64))*X^9+(C ((128*(u z))))*X^8+(C ((-176+(64*((u z))^2))))*X^7+(C ((-288*(u z))))*X^6+(C ((168+(-112*((u z))^2))))*X^5+(C ((208*(u z))))*X^4+(C ((-63+(56*((u z))^2))))*X^3+(C (((-64*((G z))^7)+(-56*((G z))^3)+(-50*(u z))+(7*(G z))+(112*((G z))^5))))*X^2+(C ((7+(-7*((u z))^2))))*X^1+(C (((-112*((G z))^5)+(-7*(G z))+(2*(u z))+(56*((G z))^3)+(64*((G z))^7)+(-64*((G z))^7*((u z))^2)+(-56*((G z))^3*((u z))^2)+(7*(G z)*((u z))^2)+(112*((G z))^5*((u z))^2))))*X^0) := by
    rw [Tpoly7,Upoly6]
    norm_num [Spectral.chebT,Tpoly7,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly6]
  ring

/-- Article: exact quadratic-moment source of raw upper7. -/
theorem upper7_source (z : ℝ) : reducedSlack z 7 (1 : ℝ)=((64*(moment z 9))+((moment z 0)*((-112*((G z))^5)+(-7*(G z))+(-2*(u z))+(56*((G z))^3)+(64*((G z))^7)+(-64*((G z))^7*((u z))^2)+(-56*((G z))^3*((u z))^2)+(7*(G z)*((u z))^2)+(112*((G z))^5*((u z))^2)))+((moment z 1)*(7+(-7*((u z))^2)))+((moment z 2)*((-64*((G z))^7)+(-56*((G z))^3)+(7*(G z))+(50*(u z))+(112*((G z))^5)))+((moment z 3)*(-63+(56*((u z))^2)))+((moment z 5)*(168+(-112*((u z))^2)))+((moment z 7)*(-176+(64*((u z))^2)))+(-1*(d z)*(-1+(-80*((G z))^4)+(24*((G z))^2)+(64*((G z))^6)))+(-208*(moment z 4)*(u z))+(-128*(moment z 8)*(u z))+(288*(moment z 6)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 7 (G z))-Chebyshev.T ℝ 7)+
        C ((1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 6=((C (64))*X^9+(C ((-128*(u z))))*X^8+(C ((-176+(64*((u z))^2))))*X^7+(C ((288*(u z))))*X^6+(C ((168+(-112*((u z))^2))))*X^5+(C ((-208*(u z))))*X^4+(C ((-63+(56*((u z))^2))))*X^3+(C (((-64*((G z))^7)+(-56*((G z))^3)+(7*(G z))+(50*(u z))+(112*((G z))^5))))*X^2+(C ((7+(-7*((u z))^2))))*X^1+(C (((-112*((G z))^5)+(-7*(G z))+(-2*(u z))+(56*((G z))^3)+(64*((G z))^7)+(-64*((G z))^7*((u z))^2)+(-56*((G z))^3*((u z))^2)+(7*(G z)*((u z))^2)+(112*((G z))^5*((u z))^2))))*X^0) := by
    rw [Tpoly7,Upoly6]
    norm_num [Spectral.chebT,Tpoly7,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly6]
  ring

/-- Article: exact quadratic-moment source of raw lower8. -/
theorem lower8_source (z : ℝ) : reducedSlack z 8 (-1 : ℝ)=((128*(moment z 10))+((moment z 0)*((-256*((G z))^6)+(-32*((G z))^2)+(128*((G z))^8)+(160*((G z))^4)+(-160*((G z))^4*((u z))^2)+(-128*((G z))^8*((u z))^2)+(32*((G z))^2*((u z))^2)+(256*((G z))^6*((u z))^2)))+((moment z 2)*(32+(-160*((G z))^4)+(-128*((G z))^8)+(-32*((u z))^2)+(32*((G z))^2)+(256*((G z))^6)))+((moment z 4)*(-192+(160*((u z))^2)))+((moment z 6)*(416+(-256*((u z))^2)))+((moment z 8)*(-384+(128*((u z))^2)))+((d z)*((-192*((G z))^5)+(-8*(G z))+(80*((G z))^3)+(128*((G z))^7)))+(-640*(moment z 7)*(u z))+(-176*(moment z 3)*(u z))+(16*(moment z 1)*(u z))+(256*(moment z 9)*(u z))+(544*(moment z 5)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 8 (G z))-Chebyshev.T ℝ 8)+
        C ((-1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 7=((C (128))*X^10+(C ((256*(u z))))*X^9+(C ((-384+(128*((u z))^2))))*X^8+(C ((-640*(u z))))*X^7+(C ((416+(-256*((u z))^2))))*X^6+(C ((544*(u z))))*X^5+(C ((-192+(160*((u z))^2))))*X^4+(C ((-176*(u z))))*X^3+(C ((32+(-160*((G z))^4)+(-128*((G z))^8)+(-32*((u z))^2)+(32*((G z))^2)+(256*((G z))^6))))*X^2+(C ((16*(u z))))*X^1+(C (((-256*((G z))^6)+(-32*((G z))^2)+(128*((G z))^8)+(160*((G z))^4)+(-160*((G z))^4*((u z))^2)+(-128*((G z))^8*((u z))^2)+(32*((G z))^2*((u z))^2)+(256*((G z))^6*((u z))^2))))*X^0) := by
    rw [Tpoly8,Upoly7]
    norm_num [Spectral.chebT,Tpoly8,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly7]
  ring

/-- Article: exact quadratic-moment source of raw upper8. -/
theorem upper8_source (z : ℝ) : reducedSlack z 8 (1 : ℝ)=((128*(moment z 10))+((moment z 0)*((-256*((G z))^6)+(-32*((G z))^2)+(128*((G z))^8)+(160*((G z))^4)+(-160*((G z))^4*((u z))^2)+(-128*((G z))^8*((u z))^2)+(32*((G z))^2*((u z))^2)+(256*((G z))^6*((u z))^2)))+((moment z 2)*(32+(-160*((G z))^4)+(-128*((G z))^8)+(-32*((u z))^2)+(32*((G z))^2)+(256*((G z))^6)))+((moment z 4)*(-192+(160*((u z))^2)))+((moment z 6)*(416+(-256*((u z))^2)))+((moment z 8)*(-384+(128*((u z))^2)))+(-1*(d z)*((-192*((G z))^5)+(-8*(G z))+(80*((G z))^3)+(128*((G z))^7)))+(-544*(moment z 5)*(u z))+(-256*(moment z 9)*(u z))+(-16*(moment z 1)*(u z))+(176*(moment z 3)*(u z))+(640*(moment z 7)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 8 (G z))-Chebyshev.T ℝ 8)+
        C ((1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 7=((C (128))*X^10+(C ((-256*(u z))))*X^9+(C ((-384+(128*((u z))^2))))*X^8+(C ((640*(u z))))*X^7+(C ((416+(-256*((u z))^2))))*X^6+(C ((-544*(u z))))*X^5+(C ((-192+(160*((u z))^2))))*X^4+(C ((176*(u z))))*X^3+(C ((32+(-160*((G z))^4)+(-128*((G z))^8)+(-32*((u z))^2)+(32*((G z))^2)+(256*((G z))^6))))*X^2+(C ((-16*(u z))))*X^1+(C (((-256*((G z))^6)+(-32*((G z))^2)+(128*((G z))^8)+(160*((G z))^4)+(-160*((G z))^4*((u z))^2)+(-128*((G z))^8*((u z))^2)+(32*((G z))^2*((u z))^2)+(256*((G z))^6*((u z))^2))))*X^0) := by
    rw [Tpoly8,Upoly7]
    norm_num [Spectral.chebT,Tpoly8,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly7]
  ring

/-- Article: exact quadratic-moment source of raw lower9. -/
theorem lower9_source (z : ℝ) : reducedSlack z 9 (-1 : ℝ)=((256*(moment z 11))+((moment z 0)*((-576*((G z))^7)+(-120*((G z))^3)+(-2*(u z))+(9*(G z))+(256*((G z))^9)+(432*((G z))^5)+(-432*((G z))^5*((u z))^2)+(-256*((G z))^9*((u z))^2)+(-9*(G z)*((u z))^2)+(120*((G z))^3*((u z))^2)+(576*((G z))^7*((u z))^2)))+((moment z 1)*(-9+(9*((u z))^2)))+((moment z 2)*((-432*((G z))^5)+(-256*((G z))^9)+(-9*(G z))+(82*(u z))+(120*((G z))^3)+(576*((G z))^7)))+((moment z 3)*(129+(-120*((u z))^2)))+((moment z 5)*(-552+(432*((u z))^2)))+((moment z 7)*(1008+(-576*((u z))^2)))+((moment z 9)*(-832+(256*((u z))^2)))+((d z)*(1+(-448*((G z))^6)+(-40*((G z))^2)+(240*((G z))^4)+(256*((G z))^8)))+(-1408*(moment z 8)*(u z))+(-560*(moment z 4)*(u z))+(512*(moment z 10)*(u z))+(1376*(moment z 6)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 9 (G z))-Chebyshev.T ℝ 9)+
        C ((-1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 8=((C (256))*X^11+(C ((512*(u z))))*X^10+(C ((-832+(256*((u z))^2))))*X^9+(C ((-1408*(u z))))*X^8+(C ((1008+(-576*((u z))^2))))*X^7+(C ((1376*(u z))))*X^6+(C ((-552+(432*((u z))^2))))*X^5+(C ((-560*(u z))))*X^4+(C ((129+(-120*((u z))^2))))*X^3+(C (((-432*((G z))^5)+(-256*((G z))^9)+(-9*(G z))+(82*(u z))+(120*((G z))^3)+(576*((G z))^7))))*X^2+(C ((-9+(9*((u z))^2))))*X^1+(C (((-576*((G z))^7)+(-120*((G z))^3)+(-2*(u z))+(9*(G z))+(256*((G z))^9)+(432*((G z))^5)+(-432*((G z))^5*((u z))^2)+(-256*((G z))^9*((u z))^2)+(-9*(G z)*((u z))^2)+(120*((G z))^3*((u z))^2)+(576*((G z))^7*((u z))^2))))*X^0) := by
    rw [Tpoly9,Upoly8]
    norm_num [Spectral.chebT,Tpoly9,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly8]
  ring

/-- Article: exact quadratic-moment source of raw upper9. -/
theorem upper9_source (z : ℝ) : reducedSlack z 9 (1 : ℝ)=((256*(moment z 11))+((moment z 0)*((-576*((G z))^7)+(-120*((G z))^3)+(2*(u z))+(9*(G z))+(256*((G z))^9)+(432*((G z))^5)+(-432*((G z))^5*((u z))^2)+(-256*((G z))^9*((u z))^2)+(-9*(G z)*((u z))^2)+(120*((G z))^3*((u z))^2)+(576*((G z))^7*((u z))^2)))+((moment z 1)*(-9+(9*((u z))^2)))+((moment z 2)*((-432*((G z))^5)+(-256*((G z))^9)+(-82*(u z))+(-9*(G z))+(120*((G z))^3)+(576*((G z))^7)))+((moment z 3)*(129+(-120*((u z))^2)))+((moment z 5)*(-552+(432*((u z))^2)))+((moment z 7)*(1008+(-576*((u z))^2)))+((moment z 9)*(-832+(256*((u z))^2)))+(-1*(d z)*(1+(-448*((G z))^6)+(-40*((G z))^2)+(240*((G z))^4)+(256*((G z))^8)))+(-1376*(moment z 6)*(u z))+(-512*(moment z 10)*(u z))+(560*(moment z 4)*(u z))+(1408*(moment z 8)*(u z))) := by
  have hpoly :
      (1-X^2-C (u z^2))*(C (Spectral.chebT 9 (G z))-Chebyshev.T ℝ 9)+
        C ((1 : ℝ)*2*u z)*(1-X^2)*Chebyshev.U ℝ 8=((C (256))*X^11+(C ((-512*(u z))))*X^10+(C ((-832+(256*((u z))^2))))*X^9+(C ((1408*(u z))))*X^8+(C ((1008+(-576*((u z))^2))))*X^7+(C ((-1376*(u z))))*X^6+(C ((-552+(432*((u z))^2))))*X^5+(C ((560*(u z))))*X^4+(C ((129+(-120*((u z))^2))))*X^3+(C (((-432*((G z))^5)+(-256*((G z))^9)+(-82*(u z))+(-9*(G z))+(120*((G z))^3)+(576*((G z))^7))))*X^2+(C ((-9+(9*((u z))^2))))*X^1+(C (((-576*((G z))^7)+(-120*((G z))^3)+(2*(u z))+(9*(G z))+(256*((G z))^9)+(432*((G z))^5)+(-432*((G z))^5*((u z))^2)+(-256*((G z))^9*((u z))^2)+(-9*(G z)*((u z))^2)+(120*((G z))^3*((u z))^2)+(576*((G z))^7*((u z))^2))))*X^0) := by
    rw [Tpoly9,Upoly8]
    norm_num [Spectral.chebT,Tpoly9,map_add,map_mul,map_sub,map_neg,map_pow,Polynomial.C_ofNat]
    ring
  unfold reducedSlack
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hpoly ⊢
  rw [hpoly]
  simp only [(momentLinear z).map_add,momentLinear_C_mul_X_pow]
  norm_num [Spectral.chebU,Upoly8]
  ring

end
end polyak.Boundary.P2
