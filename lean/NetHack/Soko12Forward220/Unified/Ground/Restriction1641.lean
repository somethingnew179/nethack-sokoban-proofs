import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1641_0_checked : (List.range' 840192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1641_1_checked : (List.range' 840320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1641_2_checked : (List.range' 840448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1641_3_checked : (List.range' 840576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1641_range (index : Nat) (lower : 840192 ≤ index) (upper : index < 840704) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 840448 then
    if cut : index < 840320 then
      exact segment_sound _ 840192 128 Restriction1641_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 840320 128 Restriction1641_1_checked index (by omega) (by omega)
  else
    if cut : index < 840576 then
      exact segment_sound _ 840448 128 Restriction1641_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 840576 128 Restriction1641_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
