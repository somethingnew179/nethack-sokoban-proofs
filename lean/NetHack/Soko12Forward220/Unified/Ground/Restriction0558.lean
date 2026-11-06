import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0558_0_checked : (List.range' 285696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0558_1_checked : (List.range' 285824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0558_2_checked : (List.range' 285952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0558_3_checked : (List.range' 286080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0558_range (index : Nat) (lower : 285696 ≤ index) (upper : index < 286208) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 285952 then
    if cut : index < 285824 then
      exact segment_sound _ 285696 128 Restriction0558_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 285824 128 Restriction0558_1_checked index (by omega) (by omega)
  else
    if cut : index < 286080 then
      exact segment_sound _ 285952 128 Restriction0558_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 286080 128 Restriction0558_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
