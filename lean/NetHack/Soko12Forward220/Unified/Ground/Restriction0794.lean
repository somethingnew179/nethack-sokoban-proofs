import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0794_0_checked : (List.range' 406528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0794_1_checked : (List.range' 406656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0794_2_checked : (List.range' 406784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0794_3_checked : (List.range' 406912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0794_range (index : Nat) (lower : 406528 ≤ index) (upper : index < 407040) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 406784 then
    if cut : index < 406656 then
      exact segment_sound _ 406528 128 Restriction0794_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 406656 128 Restriction0794_1_checked index (by omega) (by omega)
  else
    if cut : index < 406912 then
      exact segment_sound _ 406784 128 Restriction0794_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 406912 128 Restriction0794_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
