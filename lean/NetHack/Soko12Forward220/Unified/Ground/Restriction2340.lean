import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2340_0_checked : (List.range' 1198080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2340_1_checked : (List.range' 1198208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2340_2_checked : (List.range' 1198336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2340_3_checked : (List.range' 1198464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2340_range (index : Nat) (lower : 1198080 ≤ index) (upper : index < 1198592) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1198336 then
    if cut : index < 1198208 then
      exact segment_sound _ 1198080 128 Restriction2340_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1198208 128 Restriction2340_1_checked index (by omega) (by omega)
  else
    if cut : index < 1198464 then
      exact segment_sound _ 1198336 128 Restriction2340_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1198464 128 Restriction2340_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
