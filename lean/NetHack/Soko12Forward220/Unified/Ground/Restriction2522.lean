import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2522_0_checked : (List.range' 1291264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2522_1_checked : (List.range' 1291392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2522_2_checked : (List.range' 1291520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2522_3_checked : (List.range' 1291648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2522_range (index : Nat) (lower : 1291264 ≤ index) (upper : index < 1291776) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1291520 then
    if cut : index < 1291392 then
      exact segment_sound _ 1291264 128 Restriction2522_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1291392 128 Restriction2522_1_checked index (by omega) (by omega)
  else
    if cut : index < 1291648 then
      exact segment_sound _ 1291520 128 Restriction2522_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1291648 128 Restriction2522_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
