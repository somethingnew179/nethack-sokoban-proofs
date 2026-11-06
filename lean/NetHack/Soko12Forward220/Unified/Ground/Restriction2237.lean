import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2237_0_checked : (List.range' 1145344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2237_1_checked : (List.range' 1145472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2237_2_checked : (List.range' 1145600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2237_3_checked : (List.range' 1145728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2237_range (index : Nat) (lower : 1145344 ≤ index) (upper : index < 1145856) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1145600 then
    if cut : index < 1145472 then
      exact segment_sound _ 1145344 128 Restriction2237_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1145472 128 Restriction2237_1_checked index (by omega) (by omega)
  else
    if cut : index < 1145728 then
      exact segment_sound _ 1145600 128 Restriction2237_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1145728 128 Restriction2237_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
