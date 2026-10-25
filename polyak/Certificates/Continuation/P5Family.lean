import polyak.Numerics.Parametric.ChainFamily
import polyak.Certificates.Continuation.P5Cover
import polyak.Certificates.Continuation.P5Links.Link000
import polyak.Certificates.Continuation.P5Links.Link001
import polyak.Certificates.Continuation.P5Links.Link002
import polyak.Certificates.Continuation.P5Links.Link003
import polyak.Certificates.Continuation.P5Links.Link004
import polyak.Certificates.Continuation.P5Links.Link005
import polyak.Certificates.Continuation.P5Links.Link006
import polyak.Certificates.Continuation.P5Links.Link007
import polyak.Certificates.Continuation.P5Links.Link008
import polyak.Certificates.Continuation.P5Links.Link009
import polyak.Certificates.Continuation.P5Links.Link010
import polyak.Certificates.Continuation.P5Links.Link011
import polyak.Certificates.Continuation.P5Links.Link012
import polyak.Certificates.Continuation.P5Links.Link013
import polyak.Certificates.Continuation.P5Links.Link014
import polyak.Certificates.Continuation.P5Links.Link015
import polyak.Certificates.Continuation.P5Links.Link016
import polyak.Certificates.Continuation.P5Links.Link017
import polyak.Certificates.Continuation.P5Links.Link018

/-! Article: Appendix B P5 continuation, compatible complete finite chain. -/
namespace polyak.Certificates.Continuation.P5
open LeanCert.Core Numerics.Parametric

def table : Fin 20 → Slab 7 := ![⟨Batch000.I0,Batch000.C0⟩,⟨Batch001.I0,Batch001.C0⟩,⟨Batch002.I0,Batch002.C0⟩,⟨Batch003.I0,Batch003.C0⟩,⟨Batch004.I0,Batch004.C0⟩,⟨Batch005.I0,Batch005.C0⟩,⟨Batch006.I0,Batch006.C0⟩,⟨Batch007.I0,Batch007.C0⟩,⟨Batch008.I0,Batch008.C0⟩,⟨Batch009.I0,Batch009.C0⟩,⟨Batch010.I0,Batch010.C0⟩,⟨Batch011.I0,Batch011.C0⟩,⟨Batch012.I0,Batch012.C0⟩,⟨Batch013.I0,Batch013.C0⟩,⟨Batch014.I0,Batch014.C0⟩,⟨Batch015.I0,Batch015.C0⟩,⟨Batch016.I0,Batch016.C0⟩,⟨Batch017.I0,Batch017.C0⟩,⟨Batch018.I0,Batch018.C0⟩,⟨Batch019.I0,Batch019.C0⟩]

theorem table_list : List.ofFn table=slabs := by rfl

theorem chain : ChainFamily system {precision:=-80} table where
  checked := by
    intro i
    fin_cases i
    · change checkCorrelated system Batch000.I0 Batch000.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch000.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch000.accepted
    · change checkCorrelated system Batch001.I0 Batch001.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch001.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch001.accepted
    · change checkCorrelated system Batch002.I0 Batch002.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch002.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch002.accepted
    · change checkCorrelated system Batch003.I0 Batch003.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch003.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch003.accepted
    · change checkCorrelated system Batch004.I0 Batch004.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch004.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch004.accepted
    · change checkCorrelated system Batch005.I0 Batch005.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch005.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch005.accepted
    · change checkCorrelated system Batch006.I0 Batch006.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch006.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch006.accepted
    · change checkCorrelated system Batch007.I0 Batch007.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch007.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch007.accepted
    · change checkCorrelated system Batch008.I0 Batch008.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch008.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch008.accepted
    · change checkCorrelated system Batch009.I0 Batch009.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch009.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch009.accepted
    · change checkCorrelated system Batch010.I0 Batch010.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch010.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch010.accepted
    · change checkCorrelated system Batch011.I0 Batch011.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch011.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch011.accepted
    · change checkCorrelated system Batch012.I0 Batch012.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch012.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch012.accepted
    · change checkCorrelated system Batch013.I0 Batch013.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch013.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch013.accepted
    · change checkCorrelated system Batch014.I0 Batch014.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch014.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch014.accepted
    · change checkCorrelated system Batch015.I0 Batch015.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch015.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch015.accepted
    · change checkCorrelated system Batch016.I0 Batch016.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch016.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch016.accepted
    · change checkCorrelated system Batch017.I0 Batch017.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch017.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch017.accepted
    · change checkCorrelated system Batch018.I0 Batch018.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch018.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch018.accepted
    · change checkCorrelated system Batch019.I0 Batch019.C0 {precision:=-80}=true
      simpa only [allCorrelatedAccepted,Batch019.slabs,List.all_cons,List.all_nil,Bool.and_true] using Batch019.accepted
  seam := by kernel_decide
  gap := by kernel_decide
  linked := by
    intro i
    fin_cases i
    · change checkCorrelatedEndpoint system Batch000.C0 Batch001.C0 Batch000.I0.hi {precision:=-80}=true
      exact Link000.accepted
    · change checkCorrelatedEndpoint system Batch001.C0 Batch002.C0 Batch001.I0.hi {precision:=-80}=true
      exact Link001.accepted
    · change checkCorrelatedEndpoint system Batch002.C0 Batch003.C0 Batch002.I0.hi {precision:=-80}=true
      exact Link002.accepted
    · change checkCorrelatedEndpoint system Batch003.C0 Batch004.C0 Batch003.I0.hi {precision:=-80}=true
      exact Link003.accepted
    · change checkCorrelatedEndpoint system Batch004.C0 Batch005.C0 Batch004.I0.hi {precision:=-80}=true
      exact Link004.accepted
    · change checkCorrelatedEndpoint system Batch005.C0 Batch006.C0 Batch005.I0.hi {precision:=-80}=true
      exact Link005.accepted
    · change checkCorrelatedEndpoint system Batch006.C0 Batch007.C0 Batch006.I0.hi {precision:=-80}=true
      exact Link006.accepted
    · change checkCorrelatedEndpoint system Batch007.C0 Batch008.C0 Batch007.I0.hi {precision:=-80}=true
      exact Link007.accepted
    · change checkCorrelatedEndpoint system Batch008.C0 Batch009.C0 Batch008.I0.hi {precision:=-80}=true
      exact Link008.accepted
    · change checkCorrelatedEndpoint system Batch009.C0 Batch010.C0 Batch009.I0.hi {precision:=-80}=true
      exact Link009.accepted
    · change checkCorrelatedEndpoint system Batch010.C0 Batch011.C0 Batch010.I0.hi {precision:=-80}=true
      exact Link010.accepted
    · change checkCorrelatedEndpoint system Batch011.C0 Batch012.C0 Batch011.I0.hi {precision:=-80}=true
      exact Link011.accepted
    · change checkCorrelatedEndpoint system Batch012.C0 Batch013.C0 Batch012.I0.hi {precision:=-80}=true
      exact Link012.accepted
    · change checkCorrelatedEndpoint system Batch013.C0 Batch014.C0 Batch013.I0.hi {precision:=-80}=true
      exact Link013.accepted
    · change checkCorrelatedEndpoint system Batch014.C0 Batch015.C0 Batch014.I0.hi {precision:=-80}=true
      exact Link014.accepted
    · change checkCorrelatedEndpoint system Batch015.C0 Batch016.C0 Batch015.I0.hi {precision:=-80}=true
      exact Link015.accepted
    · change checkCorrelatedEndpoint system Batch016.C0 Batch017.C0 Batch016.I0.hi {precision:=-80}=true
      exact Link016.accepted
    · change checkCorrelatedEndpoint system Batch017.C0 Batch018.C0 Batch017.I0.hi {precision:=-80}=true
      exact Link017.accepted
    · change checkCorrelatedEndpoint system Batch018.C0 Batch019.C0 Batch018.I0.hi {precision:=-80}=true
      exact Link018.accepted

end polyak.Certificates.Continuation.P5
