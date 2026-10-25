import polyak.Certificates.Continuation.P5Slope.Batch000
import polyak.Certificates.Continuation.P5Slope.Batch001
import polyak.Certificates.Continuation.P5Slope.Batch002
import polyak.Certificates.Continuation.P5Slope.Batch003
import polyak.Certificates.Continuation.P5Slope.Batch004
import polyak.Certificates.Continuation.P5Slope.Batch005
import polyak.Certificates.Continuation.P5Slope.Batch006
import polyak.Certificates.Continuation.P5Slope.Batch007
import polyak.Certificates.Continuation.P5Slope.Batch008
import polyak.Certificates.Continuation.P5Slope.Batch009
import polyak.Certificates.Continuation.P5Slope.Batch010
import polyak.Certificates.Continuation.P5Slope.Batch011
import polyak.Certificates.Continuation.P5Slope.Batch012
import polyak.Certificates.Continuation.P5Slope.Batch013
import polyak.Certificates.Continuation.P5Slope.Batch014
import polyak.Certificates.Continuation.P5Slope.Batch015
import polyak.Certificates.Continuation.P5Slope.Batch016
import polyak.Certificates.Continuation.P5Slope.Batch017
import polyak.Certificates.Continuation.P5Slope.Batch018
import polyak.Certificates.Continuation.P5Slope.Batch019
import polyak.Certificates.Continuation.P5Family

/-! Article: complete checked derivative reserves on the actual source cover. -/
namespace polyak.Certificates.Continuation.P5.Slope
open LeanCert.Core Numerics.Parametric Boundary.P5

def center : Fin 20 → (Fin 7 → ℚ) := ![Batch000.center,Batch001.center,Batch002.center,Batch003.center,Batch004.center,Batch005.center,Batch006.center,Batch007.center,Batch008.center,Batch009.center,Batch010.center,Batch011.center,Batch012.center,Batch013.center,Batch014.center,Batch015.center,Batch016.center,Batch017.center,Batch018.center,Batch019.center]

def radius : Fin 20 → (Fin 7 → ℚ) := ![Batch000.radius,Batch001.radius,Batch002.radius,Batch003.radius,Batch004.radius,Batch005.radius,Batch006.radius,Batch007.radius,Batch008.radius,Batch009.radius,Batch010.radius,Batch011.radius,Batch012.radius,Batch013.radius,Batch014.radius,Batch015.radius,Batch016.radius,Batch017.radius,Batch018.radius,Batch019.radius]

theorem checked (i : Fin 20) :
    ∃ (J : Matrix (Fin 7) (Fin 7) IntervalRat) (p : Fin 7 → IntervalRat),
      derivativeEnclosureCheck P5.system (P5.table i).domain
        (coordinateBox (P5.table i).certificate.center (P5.table i).certificate.radius)
        J p {precision:=-80}=true ∧
      sourceSlopeCheck (P5.table i).domain (P5.table i).certificate
        (center i) (radius i) J p=true := by
  fin_cases i
  · exact ⟨Batch000.jacobianBox,Batch000.parameterBox,Batch000.derivatives,Batch000.accepted⟩
  · exact ⟨Batch001.jacobianBox,Batch001.parameterBox,Batch001.derivatives,Batch001.accepted⟩
  · exact ⟨Batch002.jacobianBox,Batch002.parameterBox,Batch002.derivatives,Batch002.accepted⟩
  · exact ⟨Batch003.jacobianBox,Batch003.parameterBox,Batch003.derivatives,Batch003.accepted⟩
  · exact ⟨Batch004.jacobianBox,Batch004.parameterBox,Batch004.derivatives,Batch004.accepted⟩
  · exact ⟨Batch005.jacobianBox,Batch005.parameterBox,Batch005.derivatives,Batch005.accepted⟩
  · exact ⟨Batch006.jacobianBox,Batch006.parameterBox,Batch006.derivatives,Batch006.accepted⟩
  · exact ⟨Batch007.jacobianBox,Batch007.parameterBox,Batch007.derivatives,Batch007.accepted⟩
  · exact ⟨Batch008.jacobianBox,Batch008.parameterBox,Batch008.derivatives,Batch008.accepted⟩
  · exact ⟨Batch009.jacobianBox,Batch009.parameterBox,Batch009.derivatives,Batch009.accepted⟩
  · exact ⟨Batch010.jacobianBox,Batch010.parameterBox,Batch010.derivatives,Batch010.accepted⟩
  · exact ⟨Batch011.jacobianBox,Batch011.parameterBox,Batch011.derivatives,Batch011.accepted⟩
  · exact ⟨Batch012.jacobianBox,Batch012.parameterBox,Batch012.derivatives,Batch012.accepted⟩
  · exact ⟨Batch013.jacobianBox,Batch013.parameterBox,Batch013.derivatives,Batch013.accepted⟩
  · exact ⟨Batch014.jacobianBox,Batch014.parameterBox,Batch014.derivatives,Batch014.accepted⟩
  · exact ⟨Batch015.jacobianBox,Batch015.parameterBox,Batch015.derivatives,Batch015.accepted⟩
  · exact ⟨Batch016.jacobianBox,Batch016.parameterBox,Batch016.derivatives,Batch016.accepted⟩
  · exact ⟨Batch017.jacobianBox,Batch017.parameterBox,Batch017.derivatives,Batch017.accepted⟩
  · exact ⟨Batch018.jacobianBox,Batch018.parameterBox,Batch018.derivatives,Batch018.accepted⟩
  · exact ⟨Batch019.jacobianBox,Batch019.parameterBox,Batch019.derivatives,Batch019.accepted⟩

end polyak.Certificates.Continuation.P5.Slope
