import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0495_0_checked : (List.range' 253440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0495_1_checked : (List.range' 253568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0495_2_checked : (List.range' 253696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0495_3_checked : (List.range' 253824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0495_range (index : Nat) (lower : 253440 ≤ index) (upper : index < 253952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 253696 then
    if cut : index < 253568 then
      exact segment_sound _ 253440 128 Restriction0495_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 253568 128 Restriction0495_1_checked index (by omega) (by omega)
  else
    if cut : index < 253824 then
      exact segment_sound _ 253696 128 Restriction0495_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 253824 128 Restriction0495_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
