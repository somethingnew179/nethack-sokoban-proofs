import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2252_0_checked : (List.range' 1153024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2252_1_checked : (List.range' 1153152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2252_2_checked : (List.range' 1153280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2252_3_checked : (List.range' 1153408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2252_range (index : Nat) (lower : 1153024 ≤ index) (upper : index < 1153536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1153280 then
    if cut : index < 1153152 then
      exact segment_sound _ 1153024 128 Restriction2252_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1153152 128 Restriction2252_1_checked index (by omega) (by omega)
  else
    if cut : index < 1153408 then
      exact segment_sound _ 1153280 128 Restriction2252_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1153408 128 Restriction2252_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
