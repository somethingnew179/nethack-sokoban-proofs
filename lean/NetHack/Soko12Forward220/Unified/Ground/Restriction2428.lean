import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2428_0_checked : (List.range' 1243136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2428_1_checked : (List.range' 1243264 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2428_2_checked : (List.range' 1243392 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2428_3_checked : (List.range' 1243520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2428_range (index : Nat) (lower : 1243136 ≤ index) (upper : index < 1243648) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1243392 then
    if cut : index < 1243264 then
      exact segment_sound _ 1243136 128 Restriction2428_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1243264 128 Restriction2428_1_checked index (by omega) (by omega)
  else
    if cut : index < 1243520 then
      exact segment_sound _ 1243392 128 Restriction2428_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1243520 128 Restriction2428_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
