import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1118_0_checked : (List.range' 572416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1118_1_checked : (List.range' 572544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1118_2_checked : (List.range' 572672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1118_3_checked : (List.range' 572800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1118_range (index : Nat) (lower : 572416 ≤ index) (upper : index < 572928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 572672 then
    if cut : index < 572544 then
      exact segment_sound _ 572416 128 Restriction1118_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 572544 128 Restriction1118_1_checked index (by omega) (by omega)
  else
    if cut : index < 572800 then
      exact segment_sound _ 572672 128 Restriction1118_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 572800 128 Restriction1118_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
