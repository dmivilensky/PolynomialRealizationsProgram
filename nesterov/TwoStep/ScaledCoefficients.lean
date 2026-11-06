import nesterov.TwoStep.Mixed
import nesterov.TwoStep.AsymptoticsModel

/-!
Article: Lemma `lem:Pscaled`. Exact polynomial remainders for independent
accelerated parameters. Uniform compact bounds are proved in the next module.
-/
namespace nesterov.TwoStep
noncomputable section

def scaledP0 (ε c θ y τ : ℝ) : ℝ :=
  P0 (1-c*ε) (Quadratic.S (1-θ*ε) τ y (ε^2)) (Quadratic.S (1-θ*ε) τ y 1)
    (Quadratic.Q (1-θ*ε) τ y (ε^2)) (Quadratic.Q (1-θ*ε) τ y 1)
def scaledP1 (ε c θ y τ : ℝ) : ℝ :=
  P1 (1-c*ε) (Quadratic.S (1-θ*ε) τ y (ε^2)) (Quadratic.S (1-θ*ε) τ y 1)
    (Quadratic.Q (1-θ*ε) τ y (ε^2)) (Quadratic.Q (1-θ*ε) τ y 1)
def scaledP2 (ε c θ y τ : ℝ) : ℝ :=
  P2 (1-c*ε) (Quadratic.S (1-θ*ε) τ y (ε^2)) (Quadratic.S (1-θ*ε) τ y 1)
    (Quadratic.Q (1-θ*ε) τ y (ε^2)) (Quadratic.Q (1-θ*ε) τ y 1)
def scaledP3 (ε c θ y τ : ℝ) : ℝ :=
  P3 (1-c*ε) (Quadratic.Q (1-θ*ε) τ y 1)
def scaledQ0 (ε c θ y τ : ℝ) : ℝ := mixedQ0 (1-θ*ε) τ (y*ε^2) y (1-c*ε)
def scaledQ1 (ε c θ y τ : ℝ) : ℝ := mixedQ1 (1-θ*ε) τ (y*ε^2) y (1-c*ε)
def scaledQ2 (ε c θ y τ : ℝ) : ℝ := mixedQ2 (1-θ*ε) τ (y*ε^2) y (1-c*ε)

def dotP1 (c θ y _τ : ℝ) : ℝ :=
  -6*c*y+2*θ*y

def remainderP1 (ε c θ y τ : ℝ) : ℝ :=
  (15*c^2*y+2*c*θ*y*τ-4*c*θ*y+y^2)+ε*((-4*c^3*y*τ-13*c^3*y+4*c^3-c^2*θ*y*τ+3*c^2*θ*y-4*c^2*θ+2*c*θ^2+2*c*y^2*τ^2-3*c*y^2+2*c*y-2*θ*y)+ε*((4*c^4*y*τ+4*c^4*y-3*c^4-c^3*θ*y*τ-c^3*θ*y-c^2*θ^2-c^2*y^2*τ^2+2*c^2*y^2*τ+3*c^2*y^2-4*c^2*y*τ-5*c^2*y+2*c*θ*y*τ+4*c*θ*y)+ε*((-c^5+4*c^4*θ-c^3*θ^2-c^3*y^2*τ^2-2*c^3*y^2*τ-c^3*y^2+4*c^3*y*τ+3*c^3*y-c^2*θ*y*τ-c^2*θ*y)+ε*((-c^3*θ*y*τ-c^3*θ*y)))))

def dotP2 (c θ y τ : ℝ) : ℝ :=
  -16*c*y*τ+8*c*y+4*c+2*θ*y*τ

def remainderP2 (ε c θ y τ : ℝ) : ℝ :=
  (18*c^2*y*τ-12*c^2*y-4*c^2-4*c*θ*y*τ-8*c*θ+2*θ^2+2*y^2*τ^2+2*y^2*τ-4*y*τ-2*y)+ε*((-4*c^3*y*τ+8*c^3*y-4*c^3+2*c^2*θ*y*τ+14*c^2*θ-4*c*θ^2-4*c*y^2*τ^2-4*c*y^2*τ+8*c*y*τ+4*c*y+2*θ*y*τ+2*θ*y)+ε*((-2*c^4*y*τ-2*c^4*y+4*c^4-4*c^3*θ+2*c^2*θ^2+2*c^2*y^2*τ^2+2*c^2*y^2*τ-4*c^2*y*τ-2*c^2*y-4*c*θ*y*τ-4*c*θ*y)+ε*((-2*c^4*θ+2*c^2*θ*y*τ+2*c^2*θ*y))))

def dotP3 (c θ y τ : ℝ) : ℝ :=
  12*c*y*τ-12*c-4*θ

def remainderP3 (ε c θ y τ : ℝ) : ℝ :=
  (-12*c^2*y*τ+12*c^2+12*c*θ)+ε*((4*c^3*y*τ-4*c^3-12*c^2*θ)+ε*((4*c^3*θ)))

def dotQ0 (c θ y _τ : ℝ) : ℝ :=
  -4*c*y+2*θ*y

def remainderQ0 (ε c θ y τ : ℝ) : ℝ :=
  (2*c^2*y*τ+7*c^2*y-3*c*θ*y+y^2)+ε*((-3*c^3*y*τ-3*c^3*y+c^2*θ*y*τ+c^2*θ*y-2*c*y^2*τ-2*c*y^2+4*c*y-2*θ*y)+ε*((c^4-2*c^3*θ+c^2*θ^2+c^2*y^2*τ^2+2*c^2*y^2*τ+c^2*y^2-2*c^2*y*τ-5*c^2*y+c*θ*y)+ε*((c^3*y*τ+c^3*y+c^2*θ*y*τ+c^2*θ*y))))

def dotQ1 (c θ y τ : ℝ) : ℝ :=
  -10*c*y*τ+6*c*y+2*θ*y*τ

def remainderQ1 (ε c θ y τ : ℝ) : ℝ :=
  (4*c^2*y*τ-6*c^2*y+4*c^2-2*c*θ*y*τ-4*c*θ+2*θ^2+2*y^2*τ^2+2*y^2*τ-4*y*τ-2*y)+ε*((2*c^3*y*τ+2*c^3*y-4*c^3+2*c^2*θ-2*c*θ^2-2*c*y^2*τ^2-2*c*y^2*τ+6*c*y*τ+2*c*y+2*θ*y*τ+2*θ*y)+ε*((2*c^3*θ-2*c^2*y*τ-2*c*θ*y*τ-2*c*θ*y)))

def dotQ2 (c θ y τ : ℝ) : ℝ :=
  8*c*y*τ-8*c-4*θ

def remainderQ2 (ε c θ y τ : ℝ) : ℝ :=
  (-4*c^2*y*τ+4*c^2+8*c*θ)+ε*((-4*c^2*θ))

theorem scaledP0_exact (ε c θ y τ : ℝ) :
    scaledP0 ε c θ y τ=c*ε*realCharacteristic (1-θ*ε) τ y (ε^2) (1-c*ε)*
      realCharacteristic (1-θ*ε) τ y 1 (1-c*ε) := by
  unfold scaledP0 P0 realCharacteristic
  ring

theorem scaled_chiL_exact (ε c θ y τ : ℝ) :
    realCharacteristic (1-θ*ε) τ y 1 (1-c*ε)=
      y+ε*(-y*(1+τ)*c+ε*(c^2-θ*c)) := by
  unfold realCharacteristic Quadratic.S Quadratic.Q
  ring

theorem scaledP1_exact (ε c θ y τ : ℝ) :
    scaledP1 ε c θ y τ=ε*dotP1 c θ y τ+ε^2*remainderP1 ε c θ y τ := by
  unfold scaledP1 P1 E0 E1 E2 Quadratic.S Quadratic.Q dotP1 remainderP1
  ring

theorem scaledP2_exact (ε c θ y τ : ℝ) :
    scaledP2 ε c θ y τ=2*y*(2*τ-1)+ε*dotP2 c θ y τ+ε^2*remainderP2 ε c θ y τ := by
  unfold scaledP2 P2 E1 Quadratic.S Quadratic.Q dotP2 remainderP2
  ring

theorem scaledP3_exact (ε c θ y τ : ℝ) :
    scaledP3 ε c θ y τ=4*(1-τ*y)+ε*dotP3 c θ y τ+ε^2*remainderP3 ε c θ y τ := by
  unfold scaledP3 P3 Quadratic.Q dotP3 remainderP3
  ring

theorem scaledQ0_exact (ε c θ y τ : ℝ) :
    scaledQ0 ε c θ y τ=ε*dotQ0 c θ y τ+ε^2*remainderQ0 ε c θ y τ := by
  unfold scaledQ0 mixedQ0 mixedPolynomial mixedBracket E0 E1 E2 Quadratic.S Quadratic.Q dotQ0 remainderQ0
  ring

theorem scaledQ1_exact (ε c θ y τ : ℝ) :
    scaledQ1 ε c θ y τ=2*y*(2*τ-1)+ε*dotQ1 c θ y τ+ε^2*remainderQ1 ε c θ y τ := by
  unfold scaledQ1 mixedQ1 mixedBracket E1 E2 Quadratic.S Quadratic.Q dotQ1 remainderQ1
  ring

theorem scaledQ2_exact (ε c θ y τ : ℝ) :
    scaledQ2 ε c θ y τ=4*(1-τ*y)+ε*dotQ2 c θ y τ+ε^2*remainderQ2 ε c θ y τ := by
  unfold scaledQ2 mixedQ2 Quadratic.Q dotQ2 remainderQ2
  ring

theorem scaled_cross_im (ε c θ y τ ω : ℝ) :
    (Quadratic.characteristic (1-θ*ε) τ 1 (y*ε^2) (circle (1-c*ε) ω)*
      star (Quadratic.characteristic (1-θ*ε) τ 1 y (circle (1-c*ε) ω))).im=
      (y-y*ε^2)*(1-c*ε)*Real.sin ω*
        (ε*(θ-2*c)+(1+τ)*c^2*ε^2+2*τ*(1-c*ε)*(1-Real.cos ω)) := by
  rw [cross_im_circle]
  unfold mixedBracket
  ring

theorem corner_dots (c θ : ℝ) :
    dotP1 c θ 2 (1/2)=4*(θ-3*c) ∧ dotP2 c θ 2 (1/2)=2*(θ+2*c) ∧
      dotP3 c θ 2 (1/2)= -4*θ ∧ dotQ0 c θ 2 (1/2)=4*(θ-2*c) ∧
        dotQ1 c θ 2 (1/2)=2*(θ+c) ∧ dotQ2 c θ 2 (1/2)= -4*θ := by
  unfold dotP1 dotP2 dotP3 dotQ0 dotQ1 dotQ2
  exact ⟨by ring,by ring,by ring,by ring,by ring,by ring⟩

end
end nesterov.TwoStep
