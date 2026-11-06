import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1510_0_checked : (List.range' 773120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1510_1_checked : (List.range' 773248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1510_2_checked : (List.range' 773376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1510_3_checked : (List.range' 773504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1510_range (index : Nat) (lower : 773120 ≤ index) (upper : index < 773632) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 773376 then
    if cut : index < 773248 then
      exact segment_sound _ 773120 128 Restriction1510_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 773248 128 Restriction1510_1_checked index (by omega) (by omega)
  else
    if cut : index < 773504 then
      exact segment_sound _ 773376 128 Restriction1510_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 773504 128 Restriction1510_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
