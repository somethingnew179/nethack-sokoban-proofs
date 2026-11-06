import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2623_0_checked : (List.range' 1342976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2623_1_checked : (List.range' 1343104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2623_2_checked : (List.range' 1343232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2623_3_checked : (List.range' 1343360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2623_range (index : Nat) (lower : 1342976 ≤ index) (upper : index < 1343488) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1343232 then
    if cut : index < 1343104 then
      exact segment_sound _ 1342976 128 Restriction2623_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1343104 128 Restriction2623_1_checked index (by omega) (by omega)
  else
    if cut : index < 1343360 then
      exact segment_sound _ 1343232 128 Restriction2623_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1343360 128 Restriction2623_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
