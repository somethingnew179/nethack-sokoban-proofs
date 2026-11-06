import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1148_0_checked : (List.range' 587776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1148_1_checked : (List.range' 587904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1148_2_checked : (List.range' 588032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1148_3_checked : (List.range' 588160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1148_range (index : Nat) (lower : 587776 ≤ index) (upper : index < 588288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 588032 then
    if cut : index < 587904 then
      exact segment_sound _ 587776 128 Restriction1148_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 587904 128 Restriction1148_1_checked index (by omega) (by omega)
  else
    if cut : index < 588160 then
      exact segment_sound _ 588032 128 Restriction1148_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 588160 128 Restriction1148_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
