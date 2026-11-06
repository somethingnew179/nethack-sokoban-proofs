import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1235_0_checked : (List.range' 632320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1235_1_checked : (List.range' 632448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1235_2_checked : (List.range' 632576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1235_3_checked : (List.range' 632704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1235_range (index : Nat) (lower : 632320 ≤ index) (upper : index < 632832) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 632576 then
    if cut : index < 632448 then
      exact segment_sound _ 632320 128 Restriction1235_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 632448 128 Restriction1235_1_checked index (by omega) (by omega)
  else
    if cut : index < 632704 then
      exact segment_sound _ 632576 128 Restriction1235_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 632704 128 Restriction1235_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
