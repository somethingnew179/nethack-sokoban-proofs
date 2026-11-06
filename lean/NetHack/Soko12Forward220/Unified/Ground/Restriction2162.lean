import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2162_0_checked : (List.range' 1106944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2162_1_checked : (List.range' 1107072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2162_2_checked : (List.range' 1107200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2162_3_checked : (List.range' 1107328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2162_range (index : Nat) (lower : 1106944 ≤ index) (upper : index < 1107456) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1107200 then
    if cut : index < 1107072 then
      exact segment_sound _ 1106944 128 Restriction2162_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1107072 128 Restriction2162_1_checked index (by omega) (by omega)
  else
    if cut : index < 1107328 then
      exact segment_sound _ 1107200 128 Restriction2162_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1107328 128 Restriction2162_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
