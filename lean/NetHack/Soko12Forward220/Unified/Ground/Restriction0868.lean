import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0868_0_checked : (List.range' 444416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0868_1_checked : (List.range' 444544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0868_2_checked : (List.range' 444672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0868_3_checked : (List.range' 444800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0868_range (index : Nat) (lower : 444416 ≤ index) (upper : index < 444928) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 444672 then
    if cut : index < 444544 then
      exact segment_sound _ 444416 128 Restriction0868_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 444544 128 Restriction0868_1_checked index (by omega) (by omega)
  else
    if cut : index < 444800 then
      exact segment_sound _ 444672 128 Restriction0868_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 444800 128 Restriction0868_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
