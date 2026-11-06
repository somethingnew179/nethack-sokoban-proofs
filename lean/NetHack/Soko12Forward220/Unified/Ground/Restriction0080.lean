import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0080_0_checked : (List.range' 40960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0080_1_checked : (List.range' 41088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0080_2_checked : (List.range' 41216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0080_3_checked : (List.range' 41344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0080_range (index : Nat) (lower : 40960 ≤ index) (upper : index < 41472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 41216 then
    if cut : index < 41088 then
      exact segment_sound _ 40960 128 Restriction0080_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 41088 128 Restriction0080_1_checked index (by omega) (by omega)
  else
    if cut : index < 41344 then
      exact segment_sound _ 41216 128 Restriction0080_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 41344 128 Restriction0080_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
