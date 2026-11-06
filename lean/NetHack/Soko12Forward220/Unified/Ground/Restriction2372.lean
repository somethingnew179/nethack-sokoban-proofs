import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2372_0_checked : (List.range' 1214464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2372_1_checked : (List.range' 1214592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2372_2_checked : (List.range' 1214720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2372_3_checked : (List.range' 1214848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2372_range (index : Nat) (lower : 1214464 ≤ index) (upper : index < 1214976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1214720 then
    if cut : index < 1214592 then
      exact segment_sound _ 1214464 128 Restriction2372_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1214592 128 Restriction2372_1_checked index (by omega) (by omega)
  else
    if cut : index < 1214848 then
      exact segment_sound _ 1214720 128 Restriction2372_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1214848 128 Restriction2372_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
