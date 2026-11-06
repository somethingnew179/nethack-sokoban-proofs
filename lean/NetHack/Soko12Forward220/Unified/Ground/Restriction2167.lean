import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2167_0_checked : (List.range' 1109504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2167_1_checked : (List.range' 1109632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2167_2_checked : (List.range' 1109760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2167_3_checked : (List.range' 1109888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2167_range (index : Nat) (lower : 1109504 ≤ index) (upper : index < 1110016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1109760 then
    if cut : index < 1109632 then
      exact segment_sound _ 1109504 128 Restriction2167_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1109632 128 Restriction2167_1_checked index (by omega) (by omega)
  else
    if cut : index < 1109888 then
      exact segment_sound _ 1109760 128 Restriction2167_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1109888 128 Restriction2167_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
