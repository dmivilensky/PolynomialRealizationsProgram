import polyak.Boundary.P5.SlabProperties
import polyak.Certificates.Continuation.P5Cover
import polyak.Certificates.Continuation.P5Prefix.Batch000
import polyak.Certificates.Continuation.P5Prefix.Batch001
import polyak.Certificates.Continuation.P5Prefix.Batch002
import polyak.Certificates.Continuation.P5Prefix.Batch003
import polyak.Certificates.Continuation.P5Prefix.Batch004
import polyak.Certificates.Continuation.P5Prefix.Batch005
import polyak.Certificates.Continuation.P5Prefix.Batch006
import polyak.Certificates.Continuation.P5Prefix.Batch007
import polyak.Certificates.Continuation.P5Prefix.Batch008
import polyak.Certificates.Continuation.P5Prefix.Batch009
import polyak.Certificates.Continuation.P5Prefix.Batch010
import polyak.Certificates.Continuation.P5Prefix.Batch011
import polyak.Certificates.Continuation.P5Prefix.Batch012
import polyak.Certificates.Continuation.P5Prefix.Batch013
import polyak.Certificates.Continuation.P5Prefix.Batch014
import polyak.Certificates.Continuation.P5Prefix.Batch015
import polyak.Certificates.Continuation.P5Prefix.Batch016
import polyak.Certificates.Continuation.P5Prefix.Batch017
import polyak.Certificates.Continuation.P5Prefix.Batch018
import polyak.Certificates.Continuation.P5Prefix.Batch019

/-! Article: (p5arc), all finite source properties on the complete continuation cover. -/
namespace polyak.Certificates.Continuation.P5Properties
open Boundary.P5 Numerics.Parametric

private theorem prefix000 : allPrefixCheck P5Lags.codes P5.Batch000.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch000.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch000.accepted

private theorem prefix001 : allPrefixCheck P5Lags.codes P5.Batch001.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch001.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch001.accepted

private theorem prefix002 : allPrefixCheck P5Lags.codes P5.Batch002.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch002.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch002.accepted

private theorem prefix003 : allPrefixCheck P5Lags.codes P5.Batch003.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch003.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch003.accepted

private theorem prefix004 : allPrefixCheck P5Lags.codes P5.Batch004.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch004.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch004.accepted

private theorem prefix005 : allPrefixCheck P5Lags.codes P5.Batch005.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch005.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch005.accepted

private theorem prefix006 : allPrefixCheck P5Lags.codes P5.Batch006.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch006.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch006.accepted

private theorem prefix007 : allPrefixCheck P5Lags.codes P5.Batch007.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch007.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch007.accepted

private theorem prefix008 : allPrefixCheck P5Lags.codes P5.Batch008.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch008.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch008.accepted

private theorem prefix009 : allPrefixCheck P5Lags.codes P5.Batch009.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch009.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch009.accepted

private theorem prefix010 : allPrefixCheck P5Lags.codes P5.Batch010.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch010.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch010.accepted

private theorem prefix011 : allPrefixCheck P5Lags.codes P5.Batch011.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch011.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch011.accepted

private theorem prefix012 : allPrefixCheck P5Lags.codes P5.Batch012.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch012.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch012.accepted

private theorem prefix013 : allPrefixCheck P5Lags.codes P5.Batch013.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch013.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch013.accepted

private theorem prefix014 : allPrefixCheck P5Lags.codes P5.Batch014.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch014.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch014.accepted

private theorem prefix015 : allPrefixCheck P5Lags.codes P5.Batch015.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch015.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch015.accepted

private theorem prefix016 : allPrefixCheck P5Lags.codes P5.Batch016.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch016.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch016.accepted

private theorem prefix017 : allPrefixCheck P5Lags.codes P5.Batch017.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch017.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch017.accepted

private theorem prefix018 : allPrefixCheck P5Lags.codes P5.Batch018.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch018.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch018.accepted

private theorem prefix019 : allPrefixCheck P5Lags.codes P5.Batch019.slabs {precision:=-80}=true := by
  simpa only [allPrefixCheck,P5.Batch019.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch019.accepted

theorem prefixAccepted : allPrefixCheck P5Lags.codes P5.slabs {precision:=-80}=true :=
  (allPrefixCheck_append P5Lags.codes prefix000 (allPrefixCheck_append P5Lags.codes prefix001 (allPrefixCheck_append P5Lags.codes prefix002 (allPrefixCheck_append P5Lags.codes prefix003 (allPrefixCheck_append P5Lags.codes prefix004 (allPrefixCheck_append P5Lags.codes prefix005 (allPrefixCheck_append P5Lags.codes prefix006 (allPrefixCheck_append P5Lags.codes prefix007 (allPrefixCheck_append P5Lags.codes prefix008 (allPrefixCheck_append P5Lags.codes prefix009 (allPrefixCheck_append P5Lags.codes prefix010 (allPrefixCheck_append P5Lags.codes prefix011 (allPrefixCheck_append P5Lags.codes prefix012 (allPrefixCheck_append P5Lags.codes prefix013 (allPrefixCheck_append P5Lags.codes prefix014 (allPrefixCheck_append P5Lags.codes prefix015 (allPrefixCheck_append P5Lags.codes prefix016 (allPrefixCheck_append P5Lags.codes prefix017 (allPrefixCheck_append P5Lags.codes prefix018 prefix019)))))))))))))))))))

private theorem geometry000 : allGeometryCheck P5.Batch000.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch000.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch000.geometryAccepted

private theorem geometry001 : allGeometryCheck P5.Batch001.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch001.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch001.geometryAccepted

private theorem geometry002 : allGeometryCheck P5.Batch002.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch002.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch002.geometryAccepted

private theorem geometry003 : allGeometryCheck P5.Batch003.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch003.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch003.geometryAccepted

private theorem geometry004 : allGeometryCheck P5.Batch004.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch004.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch004.geometryAccepted

private theorem geometry005 : allGeometryCheck P5.Batch005.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch005.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch005.geometryAccepted

private theorem geometry006 : allGeometryCheck P5.Batch006.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch006.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch006.geometryAccepted

private theorem geometry007 : allGeometryCheck P5.Batch007.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch007.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch007.geometryAccepted

private theorem geometry008 : allGeometryCheck P5.Batch008.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch008.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch008.geometryAccepted

private theorem geometry009 : allGeometryCheck P5.Batch009.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch009.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch009.geometryAccepted

private theorem geometry010 : allGeometryCheck P5.Batch010.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch010.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch010.geometryAccepted

private theorem geometry011 : allGeometryCheck P5.Batch011.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch011.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch011.geometryAccepted

private theorem geometry012 : allGeometryCheck P5.Batch012.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch012.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch012.geometryAccepted

private theorem geometry013 : allGeometryCheck P5.Batch013.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch013.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch013.geometryAccepted

private theorem geometry014 : allGeometryCheck P5.Batch014.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch014.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch014.geometryAccepted

private theorem geometry015 : allGeometryCheck P5.Batch015.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch015.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch015.geometryAccepted

private theorem geometry016 : allGeometryCheck P5.Batch016.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch016.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch016.geometryAccepted

private theorem geometry017 : allGeometryCheck P5.Batch017.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch017.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch017.geometryAccepted

private theorem geometry018 : allGeometryCheck P5.Batch018.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch018.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch018.geometryAccepted

private theorem geometry019 : allGeometryCheck P5.Batch019.slabs {precision:=-80}=true := by
  simpa only [allGeometryCheck,P5.Batch019.slabs,List.all_cons,List.all_nil,Bool.and_true] using P5Prefix.Batch019.geometryAccepted

theorem geometryAccepted : allGeometryCheck P5.slabs {precision:=-80}=true :=
  (allGeometryCheck_append geometry000 (allGeometryCheck_append geometry001 (allGeometryCheck_append geometry002 (allGeometryCheck_append geometry003 (allGeometryCheck_append geometry004 (allGeometryCheck_append geometry005 (allGeometryCheck_append geometry006 (allGeometryCheck_append geometry007 (allGeometryCheck_append geometry008 (allGeometryCheck_append geometry009 (allGeometryCheck_append geometry010 (allGeometryCheck_append geometry011 (allGeometryCheck_append geometry012 (allGeometryCheck_append geometry013 (allGeometryCheck_append geometry014 (allGeometryCheck_append geometry015 (allGeometryCheck_append geometry016 (allGeometryCheck_append geometry017 (allGeometryCheck_append geometry018 geometry019)))))))))))))))))))

end polyak.Certificates.Continuation.P5Properties
