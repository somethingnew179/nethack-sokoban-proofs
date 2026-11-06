import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2067_0_checked : (List.range' 1058304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2067_1_checked : (List.range' 1058432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2067_2_checked : (List.range' 1058560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2067_3_checked : (List.range' 1058688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2067_range (index : Nat) (lower : 1058304 ≤ index) (upper : index < 1058816) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1058560 then
    if cut : index < 1058432 then
      exact segment_sound _ 1058304 128 Restriction2067_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1058432 128 Restriction2067_1_checked index (by omega) (by omega)
  else
    if cut : index < 1058688 then
      exact segment_sound _ 1058560 128 Restriction2067_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1058688 128 Restriction2067_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
