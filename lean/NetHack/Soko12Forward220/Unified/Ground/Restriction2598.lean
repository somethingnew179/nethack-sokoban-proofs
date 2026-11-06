import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2598_0_checked : (List.range' 1330176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2598_1_checked : (List.range' 1330304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2598_2_checked : (List.range' 1330432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2598_3_checked : (List.range' 1330560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2598_range (index : Nat) (lower : 1330176 ≤ index) (upper : index < 1330688) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1330432 then
    if cut : index < 1330304 then
      exact segment_sound _ 1330176 128 Restriction2598_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1330304 128 Restriction2598_1_checked index (by omega) (by omega)
  else
    if cut : index < 1330560 then
      exact segment_sound _ 1330432 128 Restriction2598_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1330560 128 Restriction2598_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
