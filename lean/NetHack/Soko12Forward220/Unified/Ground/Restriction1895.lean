import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1895_0_checked : (List.range' 970240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1895_1_checked : (List.range' 970368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1895_2_checked : (List.range' 970496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1895_3_checked : (List.range' 970624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1895_range (index : Nat) (lower : 970240 ≤ index) (upper : index < 970752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 970496 then
    if cut : index < 970368 then
      exact segment_sound _ 970240 128 Restriction1895_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 970368 128 Restriction1895_1_checked index (by omega) (by omega)
  else
    if cut : index < 970624 then
      exact segment_sound _ 970496 128 Restriction1895_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 970624 128 Restriction1895_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
