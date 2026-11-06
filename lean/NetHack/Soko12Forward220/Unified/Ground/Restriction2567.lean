import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2567_0_checked : (List.range' 1314304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2567_1_checked : (List.range' 1314432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2567_2_checked : (List.range' 1314560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2567_3_checked : (List.range' 1314688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2567_range (index : Nat) (lower : 1314304 ≤ index) (upper : index < 1314816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1314560 then
    if cut : index < 1314432 then
      exact segment_sound _ 1314304 128 Restriction2567_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1314432 128 Restriction2567_1_checked index (by omega) (by omega)
  else
    if cut : index < 1314688 then
      exact segment_sound _ 1314560 128 Restriction2567_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1314688 128 Restriction2567_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
