import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0737_0_checked : (List.range' 377344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0737_1_checked : (List.range' 377472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0737_2_checked : (List.range' 377600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0737_3_checked : (List.range' 377728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0737_range (index : Nat) (lower : 377344 ≤ index) (upper : index < 377856) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 377600 then
    if cut : index < 377472 then
      exact segment_sound _ 377344 128 Restriction0737_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 377472 128 Restriction0737_1_checked index (by omega) (by omega)
  else
    if cut : index < 377728 then
      exact segment_sound _ 377600 128 Restriction0737_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 377728 128 Restriction0737_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
