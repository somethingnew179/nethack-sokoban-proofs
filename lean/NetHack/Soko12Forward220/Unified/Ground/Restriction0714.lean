import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0714_0_checked : (List.range' 365568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0714_1_checked : (List.range' 365696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0714_2_checked : (List.range' 365824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0714_3_checked : (List.range' 365952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0714_range (index : Nat) (lower : 365568 ≤ index) (upper : index < 366080) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 365824 then
    if cut : index < 365696 then
      exact segment_sound _ 365568 128 Restriction0714_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 365696 128 Restriction0714_1_checked index (by omega) (by omega)
  else
    if cut : index < 365952 then
      exact segment_sound _ 365824 128 Restriction0714_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 365952 128 Restriction0714_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
