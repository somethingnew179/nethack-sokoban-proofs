import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0007_0_checked : (List.range' 3584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0007_1_checked : (List.range' 3712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0007_2_checked : (List.range' 3840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0007_3_checked : (List.range' 3968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0007_range (index : Nat) (lower : 3584 ≤ index) (upper : index < 4096) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 3840 then
    if cut : index < 3712 then
      exact segment_sound _ 3584 128 Restriction0007_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 3712 128 Restriction0007_1_checked index (by omega) (by omega)
  else
    if cut : index < 3968 then
      exact segment_sound _ 3840 128 Restriction0007_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 3968 128 Restriction0007_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
