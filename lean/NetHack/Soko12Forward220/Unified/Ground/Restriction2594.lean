import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2594_0_checked : (List.range' 1328128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2594_1_checked : (List.range' 1328256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2594_2_checked : (List.range' 1328384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2594_3_checked : (List.range' 1328512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2594_range (index : Nat) (lower : 1328128 ≤ index) (upper : index < 1328640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1328384 then
    if cut : index < 1328256 then
      exact segment_sound _ 1328128 128 Restriction2594_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1328256 128 Restriction2594_1_checked index (by omega) (by omega)
  else
    if cut : index < 1328512 then
      exact segment_sound _ 1328384 128 Restriction2594_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1328512 128 Restriction2594_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
