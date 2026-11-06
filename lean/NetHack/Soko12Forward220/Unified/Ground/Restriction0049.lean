import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0049_0_checked : (List.range' 25088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0049_1_checked : (List.range' 25216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0049_2_checked : (List.range' 25344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0049_3_checked : (List.range' 25472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0049_range (index : Nat) (lower : 25088 ≤ index) (upper : index < 25600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 25344 then
    if cut : index < 25216 then
      exact segment_sound _ 25088 128 Restriction0049_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 25216 128 Restriction0049_1_checked index (by omega) (by omega)
  else
    if cut : index < 25472 then
      exact segment_sound _ 25344 128 Restriction0049_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 25472 128 Restriction0049_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
