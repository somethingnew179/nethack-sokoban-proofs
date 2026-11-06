import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1309_0_checked : (List.range' 670208 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1309_1_checked : (List.range' 670336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1309_2_checked : (List.range' 670464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1309_3_checked : (List.range' 670592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1309_range (index : Nat) (lower : 670208 ≤ index) (upper : index < 670720) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 670464 then
    if cut : index < 670336 then
      exact segment_sound _ 670208 128 Restriction1309_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 670336 128 Restriction1309_1_checked index (by omega) (by omega)
  else
    if cut : index < 670592 then
      exact segment_sound _ 670464 128 Restriction1309_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 670592 128 Restriction1309_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
