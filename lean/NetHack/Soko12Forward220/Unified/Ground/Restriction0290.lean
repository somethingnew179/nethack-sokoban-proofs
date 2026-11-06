import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0290_0_checked : (List.range' 148480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0290_1_checked : (List.range' 148608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0290_2_checked : (List.range' 148736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0290_3_checked : (List.range' 148864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0290_range (index : Nat) (lower : 148480 ≤ index) (upper : index < 148992) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 148736 then
    if cut : index < 148608 then
      exact segment_sound _ 148480 128 Restriction0290_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 148608 128 Restriction0290_1_checked index (by omega) (by omega)
  else
    if cut : index < 148864 then
      exact segment_sound _ 148736 128 Restriction0290_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 148864 128 Restriction0290_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
