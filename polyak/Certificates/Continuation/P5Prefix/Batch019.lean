import polyak.Boundary.P5.PrefixCheck
import polyak.Boundary.P5.GeometryCheck
import polyak.Certificates.Continuation.P5LagCodes
import polyak.Certificates.Continuation.P5Batches.Batch019
import polyak.Numerics.KernelDecide

/-! Article: (p5arc), source-linked finite inactive lag certificates on slab 19.
All active slacks follow from the original source equations; every other lag
is checked after exact cancellation of the critical parameter factor. -/
namespace polyak.Certificates.Continuation.P5Prefix.Batch019
open Boundary.P5 Numerics.Parametric

private theorem lag01Upper : lagCheck 1 P5Lags.lag01 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag02Lower : lagCheck 2 P5Lags.lag02 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag03Lower : lagCheck 3 P5Lags.lag03 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag04Lower : lagCheck 4 P5Lags.lag04 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag04Upper : lagCheck 4 P5Lags.lag04 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag05Lower : lagCheck 5 P5Lags.lag05 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag06Lower : lagCheck 6 P5Lags.lag06 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag06Upper : lagCheck 6 P5Lags.lag06 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag07Lower : lagCheck 7 P5Lags.lag07 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag07Upper : lagCheck 7 P5Lags.lag07 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag08Lower : lagCheck 8 P5Lags.lag08 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag08Upper : lagCheck 8 P5Lags.lag08 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag09Lower : lagCheck 9 P5Lags.lag09 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag09Upper : lagCheck 9 P5Lags.lag09 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag10Lower : lagCheck 10 P5Lags.lag10 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag10Upper : lagCheck 10 P5Lags.lag10 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag11Lower : lagCheck 11 P5Lags.lag11 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag11Upper : lagCheck 11 P5Lags.lag11 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag12Lower : lagCheck 12 P5Lags.lag12 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag12Upper : lagCheck 12 P5Lags.lag12 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag13Lower : lagCheck 13 P5Lags.lag13 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag13Upper : lagCheck 13 P5Lags.lag13 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag14Lower : lagCheck 14 P5Lags.lag14 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag14Upper : lagCheck 14 P5Lags.lag14 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag15Lower : lagCheck 15 P5Lags.lag15 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag15Upper : lagCheck 15 P5Lags.lag15 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag16Lower : lagCheck 16 P5Lags.lag16 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag16Upper : lagCheck 16 P5Lags.lag16 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag17Lower : lagCheck 17 P5Lags.lag17 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag17Upper : lagCheck 17 P5Lags.lag17 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag18Lower : lagCheck 18 P5Lags.lag18 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag18Upper : lagCheck 18 P5Lags.lag18 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag19Lower : lagCheck 19 P5Lags.lag19 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag19Upper : lagCheck 19 P5Lags.lag19 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag20Lower : lagCheck 20 P5Lags.lag20 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag20Upper : lagCheck 20 P5Lags.lag20 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag21Lower : lagCheck 21 P5Lags.lag21 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag21Upper : lagCheck 21 P5Lags.lag21 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag22Lower : lagCheck 22 P5Lags.lag22 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag22Upper : lagCheck 22 P5Lags.lag22 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag23Lower : lagCheck 23 P5Lags.lag23 false
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

private theorem lag23Upper : lagCheck 23 P5Lags.lag23 true
    P5.Batch019.I0 (coordinateBox P5.Batch019.C0.center P5.Batch019.C0.radius) {precision:=-80}=true := by
  kernel_decide

theorem accepted : prefixCheck P5Lags.codes P5.Batch019.I0 P5.Batch019.C0 {precision:=-80}=true := by
  simp only [prefixCheck,decide_eq_true_eq]
  intro n b hn
  fin_cases n
  · norm_num at hn
  · cases b
    · exact by kernel_decide
    · exact lag01Upper
  · cases b
    · exact lag02Lower
    · exact by kernel_decide
  · cases b
    · exact lag03Lower
    · exact by kernel_decide
  · cases b
    · exact lag04Lower
    · exact lag04Upper
  · cases b
    · exact lag05Lower
    · exact by kernel_decide
  · cases b
    · exact lag06Lower
    · exact lag06Upper
  · cases b
    · exact lag07Lower
    · exact lag07Upper
  · cases b
    · exact lag08Lower
    · exact lag08Upper
  · cases b
    · exact lag09Lower
    · exact lag09Upper
  · cases b
    · exact lag10Lower
    · exact lag10Upper
  · cases b
    · exact lag11Lower
    · exact lag11Upper
  · cases b
    · exact lag12Lower
    · exact lag12Upper
  · cases b
    · exact lag13Lower
    · exact lag13Upper
  · cases b
    · exact lag14Lower
    · exact lag14Upper
  · cases b
    · exact lag15Lower
    · exact lag15Upper
  · cases b
    · exact lag16Lower
    · exact lag16Upper
  · cases b
    · exact lag17Lower
    · exact lag17Upper
  · cases b
    · exact lag18Lower
    · exact lag18Upper
  · cases b
    · exact lag19Lower
    · exact lag19Upper
  · cases b
    · exact lag20Lower
    · exact lag20Upper
  · cases b
    · exact lag21Lower
    · exact lag21Upper
  · cases b
    · exact lag22Lower
    · exact lag22Upper
  · cases b
    · exact lag23Lower
    · exact lag23Upper

theorem geometryAccepted : continuationGeometryCheck P5.Batch019.I0 P5.Batch019.C0 {precision:=-80}=true := by
  kernel_decide

end polyak.Certificates.Continuation.P5Prefix.Batch019
