import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0799_0_checked : (List.range' 409088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0799_1_checked : (List.range' 409216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0799_2_checked : (List.range' 409344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0799_3_checked : (List.range' 409472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0799_range (index : Nat) (lower : 409088 ≤ index) (upper : index < 409600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 409344 then
    if cut : index < 409216 then
      exact segment_sound _ 409088 128 Restriction0799_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 409216 128 Restriction0799_1_checked index (by omega) (by omega)
  else
    if cut : index < 409472 then
      exact segment_sound _ 409344 128 Restriction0799_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 409472 128 Restriction0799_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
