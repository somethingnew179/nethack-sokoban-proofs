import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1299_0_checked : (List.range' 665088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1299_1_checked : (List.range' 665216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1299_2_checked : (List.range' 665344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1299_3_checked : (List.range' 665472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1299_range (index : Nat) (lower : 665088 ≤ index) (upper : index < 665600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 665344 then
    if cut : index < 665216 then
      exact segment_sound _ 665088 128 Restriction1299_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 665216 128 Restriction1299_1_checked index (by omega) (by omega)
  else
    if cut : index < 665472 then
      exact segment_sound _ 665344 128 Restriction1299_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 665472 128 Restriction1299_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
