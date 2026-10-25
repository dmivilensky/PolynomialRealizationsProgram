import polyak.Certificates.Continuation.P1Slope.Batch000
import polyak.Certificates.Continuation.P1Slope.Batch001
import polyak.Certificates.Continuation.P1Slope.Batch002
import polyak.Certificates.Continuation.P1Slope.Batch003
import polyak.Certificates.Continuation.P1Slope.Batch004
import polyak.Certificates.Continuation.P1Slope.Batch005
import polyak.Certificates.Continuation.P1Slope.Batch006
import polyak.Certificates.Continuation.P1Slope.Batch007
import polyak.Certificates.Continuation.P1Slope.Batch008
import polyak.Certificates.Continuation.P1Slope.Batch009
import polyak.Certificates.Continuation.P1Slope.Batch010
import polyak.Certificates.Continuation.P1Slope.Batch011
import polyak.Certificates.Continuation.P1Slope.Batch012
import polyak.Certificates.Continuation.P1Slope.Batch013
import polyak.Certificates.Continuation.P1Slope.Batch014
import polyak.Certificates.Continuation.P1Slope.Batch015
import polyak.Certificates.Continuation.P1Cover

/-! Article: Proposition P1, full closed-domain strict source slope verification. -/
namespace polyak.Certificates.Continuation.P1.Slope
open LeanCert.Core Numerics.Parametric Boundary.P1

theorem accepted : allSourceSlopeCheck P1.system P1.slabs {precision:=-80}=true :=
  (allSourceSlopeCheck_append Batch000.accepted (allSourceSlopeCheck_append Batch001.accepted (allSourceSlopeCheck_append Batch002.accepted (allSourceSlopeCheck_append Batch003.accepted (allSourceSlopeCheck_append Batch004.accepted (allSourceSlopeCheck_append Batch005.accepted (allSourceSlopeCheck_append Batch006.accepted (allSourceSlopeCheck_append Batch007.accepted (allSourceSlopeCheck_append Batch008.accepted (allSourceSlopeCheck_append Batch009.accepted (allSourceSlopeCheck_append Batch010.accepted (allSourceSlopeCheck_append Batch011.accepted (allSourceSlopeCheck_append Batch012.accepted (allSourceSlopeCheck_append Batch013.accepted (allSourceSlopeCheck_append Batch014.accepted Batch015.accepted)))))))))))))))

end polyak.Certificates.Continuation.P1.Slope
