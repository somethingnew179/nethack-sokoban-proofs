import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1315_0_checked : (List.range' 673280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1315_1_checked : (List.range' 673408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1315_2_checked : (List.range' 673536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1315_3_checked : (List.range' 673664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1315_range (index : Nat) (lower : 673280 ≤ index) (upper : index < 673792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 673536 then
    if cut : index < 673408 then
      exact segment_sound _ 673280 128 Restriction1315_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 673408 128 Restriction1315_1_checked index (by omega) (by omega)
  else
    if cut : index < 673664 then
      exact segment_sound _ 673536 128 Restriction1315_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 673664 128 Restriction1315_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
