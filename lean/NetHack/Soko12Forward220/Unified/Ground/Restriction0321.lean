import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0321_0_checked : (List.range' 164352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0321_1_checked : (List.range' 164480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0321_2_checked : (List.range' 164608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0321_3_checked : (List.range' 164736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0321_range (index : Nat) (lower : 164352 ≤ index) (upper : index < 164864) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 164608 then
    if cut : index < 164480 then
      exact segment_sound _ 164352 128 Restriction0321_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 164480 128 Restriction0321_1_checked index (by omega) (by omega)
  else
    if cut : index < 164736 then
      exact segment_sound _ 164608 128 Restriction0321_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 164736 128 Restriction0321_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
