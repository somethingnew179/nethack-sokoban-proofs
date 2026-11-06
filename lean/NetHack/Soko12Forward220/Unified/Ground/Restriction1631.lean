import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1631_0_checked : (List.range' 835072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1631_1_checked : (List.range' 835200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1631_2_checked : (List.range' 835328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1631_3_checked : (List.range' 835456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1631_range (index : Nat) (lower : 835072 ≤ index) (upper : index < 835584) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 835328 then
    if cut : index < 835200 then
      exact segment_sound _ 835072 128 Restriction1631_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 835200 128 Restriction1631_1_checked index (by omega) (by omega)
  else
    if cut : index < 835456 then
      exact segment_sound _ 835328 128 Restriction1631_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 835456 128 Restriction1631_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
