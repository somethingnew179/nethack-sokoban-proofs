import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2618_0_checked : (List.range' 1340416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2618_1_checked : (List.range' 1340544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2618_2_checked : (List.range' 1340672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2618_3_checked : (List.range' 1340800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2618_range (index : Nat) (lower : 1340416 ≤ index) (upper : index < 1340928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1340672 then
    if cut : index < 1340544 then
      exact segment_sound _ 1340416 128 Restriction2618_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1340544 128 Restriction2618_1_checked index (by omega) (by omega)
  else
    if cut : index < 1340800 then
      exact segment_sound _ 1340672 128 Restriction2618_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1340800 128 Restriction2618_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
