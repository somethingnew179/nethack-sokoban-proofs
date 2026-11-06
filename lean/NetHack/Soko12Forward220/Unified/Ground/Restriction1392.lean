import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1392_0_checked : (List.range' 712704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1392_1_checked : (List.range' 712832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1392_2_checked : (List.range' 712960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1392_3_checked : (List.range' 713088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1392_range (index : Nat) (lower : 712704 ≤ index) (upper : index < 713216) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 712960 then
    if cut : index < 712832 then
      exact segment_sound _ 712704 128 Restriction1392_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 712832 128 Restriction1392_1_checked index (by omega) (by omega)
  else
    if cut : index < 713088 then
      exact segment_sound _ 712960 128 Restriction1392_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 713088 128 Restriction1392_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
