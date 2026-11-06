import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0745_0_checked : (List.range' 381440 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0745_1_checked : (List.range' 381568 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0745_2_checked : (List.range' 381696 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0745_3_checked : (List.range' 381824 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0745_range (index : Nat) (lower : 381440 ≤ index) (upper : index < 381952) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 381696 then
    if cut : index < 381568 then
      exact segment_sound _ 381440 128 Restriction0745_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 381568 128 Restriction0745_1_checked index (by omega) (by omega)
  else
    if cut : index < 381824 then
      exact segment_sound _ 381696 128 Restriction0745_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 381824 128 Restriction0745_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
