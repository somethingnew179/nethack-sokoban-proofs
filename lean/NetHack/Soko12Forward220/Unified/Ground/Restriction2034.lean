import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2034_0_checked : (List.range' 1041408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2034_1_checked : (List.range' 1041536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2034_2_checked : (List.range' 1041664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2034_3_checked : (List.range' 1041792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2034_range (index : Nat) (lower : 1041408 ≤ index) (upper : index < 1041920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1041664 then
    if cut : index < 1041536 then
      exact segment_sound _ 1041408 128 Restriction2034_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1041536 128 Restriction2034_1_checked index (by omega) (by omega)
  else
    if cut : index < 1041792 then
      exact segment_sound _ 1041664 128 Restriction2034_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1041792 128 Restriction2034_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
