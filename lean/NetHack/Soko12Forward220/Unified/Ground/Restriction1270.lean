import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1270_0_checked : (List.range' 650240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1270_1_checked : (List.range' 650368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1270_2_checked : (List.range' 650496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1270_3_checked : (List.range' 650624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1270_range (index : Nat) (lower : 650240 ≤ index) (upper : index < 650752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 650496 then
    if cut : index < 650368 then
      exact segment_sound _ 650240 128 Restriction1270_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 650368 128 Restriction1270_1_checked index (by omega) (by omega)
  else
    if cut : index < 650624 then
      exact segment_sound _ 650496 128 Restriction1270_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 650624 128 Restriction1270_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
