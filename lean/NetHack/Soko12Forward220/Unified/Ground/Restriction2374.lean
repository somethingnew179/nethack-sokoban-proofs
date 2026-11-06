import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2374_0_checked : (List.range' 1215488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2374_1_checked : (List.range' 1215616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2374_2_checked : (List.range' 1215744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2374_3_checked : (List.range' 1215872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2374_range (index : Nat) (lower : 1215488 ≤ index) (upper : index < 1216000) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1215744 then
    if cut : index < 1215616 then
      exact segment_sound _ 1215488 128 Restriction2374_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1215616 128 Restriction2374_1_checked index (by omega) (by omega)
  else
    if cut : index < 1215872 then
      exact segment_sound _ 1215744 128 Restriction2374_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1215872 128 Restriction2374_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
