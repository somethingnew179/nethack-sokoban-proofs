import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2536_0_checked : (List.range' 1298432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2536_1_checked : (List.range' 1298560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2536_2_checked : (List.range' 1298688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2536_3_checked : (List.range' 1298816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2536_range (index : Nat) (lower : 1298432 ≤ index) (upper : index < 1298944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1298688 then
    if cut : index < 1298560 then
      exact segment_sound _ 1298432 128 Restriction2536_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1298560 128 Restriction2536_1_checked index (by omega) (by omega)
  else
    if cut : index < 1298816 then
      exact segment_sound _ 1298688 128 Restriction2536_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1298816 128 Restriction2536_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
