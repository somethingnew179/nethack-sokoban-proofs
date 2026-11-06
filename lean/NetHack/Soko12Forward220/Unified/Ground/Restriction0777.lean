import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0777_0_checked : (List.range' 397824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0777_1_checked : (List.range' 397952 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0777_2_checked : (List.range' 398080 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0777_3_checked : (List.range' 398208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0777_range (index : Nat) (lower : 397824 ≤ index) (upper : index < 398336) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 398080 then
    if cut : index < 397952 then
      exact segment_sound _ 397824 128 Restriction0777_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 397952 128 Restriction0777_1_checked index (by omega) (by omega)
  else
    if cut : index < 398208 then
      exact segment_sound _ 398080 128 Restriction0777_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 398208 128 Restriction0777_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
