import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2561_0_checked : (List.range' 1311232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2561_1_checked : (List.range' 1311360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2561_2_checked : (List.range' 1311488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2561_3_checked : (List.range' 1311616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2561_range (index : Nat) (lower : 1311232 ≤ index) (upper : index < 1311744) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1311488 then
    if cut : index < 1311360 then
      exact segment_sound _ 1311232 128 Restriction2561_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1311360 128 Restriction2561_1_checked index (by omega) (by omega)
  else
    if cut : index < 1311616 then
      exact segment_sound _ 1311488 128 Restriction2561_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1311616 128 Restriction2561_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
