import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2534_0_checked : (List.range' 1297408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2534_1_checked : (List.range' 1297536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2534_2_checked : (List.range' 1297664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2534_3_checked : (List.range' 1297792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2534_range (index : Nat) (lower : 1297408 ≤ index) (upper : index < 1297920) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1297664 then
    if cut : index < 1297536 then
      exact segment_sound _ 1297408 128 Restriction2534_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1297536 128 Restriction2534_1_checked index (by omega) (by omega)
  else
    if cut : index < 1297792 then
      exact segment_sound _ 1297664 128 Restriction2534_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1297792 128 Restriction2534_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
