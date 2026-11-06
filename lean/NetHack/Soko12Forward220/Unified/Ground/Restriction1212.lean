import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1212_0_checked : (List.range' 620544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1212_1_checked : (List.range' 620672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1212_2_checked : (List.range' 620800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1212_3_checked : (List.range' 620928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1212_range (index : Nat) (lower : 620544 ≤ index) (upper : index < 621056) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 620800 then
    if cut : index < 620672 then
      exact segment_sound _ 620544 128 Restriction1212_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 620672 128 Restriction1212_1_checked index (by omega) (by omega)
  else
    if cut : index < 620928 then
      exact segment_sound _ 620800 128 Restriction1212_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 620928 128 Restriction1212_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
