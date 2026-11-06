import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1274_0_checked : (List.range' 652288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1274_1_checked : (List.range' 652416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1274_2_checked : (List.range' 652544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1274_3_checked : (List.range' 652672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1274_range (index : Nat) (lower : 652288 ≤ index) (upper : index < 652800) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 652544 then
    if cut : index < 652416 then
      exact segment_sound _ 652288 128 Restriction1274_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 652416 128 Restriction1274_1_checked index (by omega) (by omega)
  else
    if cut : index < 652672 then
      exact segment_sound _ 652544 128 Restriction1274_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 652672 128 Restriction1274_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
