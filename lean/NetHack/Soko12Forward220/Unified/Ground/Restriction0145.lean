import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0145_0_checked : (List.range' 74240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0145_1_checked : (List.range' 74368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0145_2_checked : (List.range' 74496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0145_3_checked : (List.range' 74624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0145_range (index : Nat) (lower : 74240 ≤ index) (upper : index < 74752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 74496 then
    if cut : index < 74368 then
      exact segment_sound _ 74240 128 Restriction0145_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 74368 128 Restriction0145_1_checked index (by omega) (by omega)
  else
    if cut : index < 74624 then
      exact segment_sound _ 74496 128 Restriction0145_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 74624 128 Restriction0145_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
