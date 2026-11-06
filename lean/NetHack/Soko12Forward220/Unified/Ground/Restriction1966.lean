import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1966_0_checked : (List.range' 1006592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1966_1_checked : (List.range' 1006720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1966_2_checked : (List.range' 1006848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1966_3_checked : (List.range' 1006976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1966_range (index : Nat) (lower : 1006592 ≤ index) (upper : index < 1007104) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1006848 then
    if cut : index < 1006720 then
      exact segment_sound _ 1006592 128 Restriction1966_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1006720 128 Restriction1966_1_checked index (by omega) (by omega)
  else
    if cut : index < 1006976 then
      exact segment_sound _ 1006848 128 Restriction1966_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1006976 128 Restriction1966_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
