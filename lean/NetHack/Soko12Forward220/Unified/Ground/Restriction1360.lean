import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1360_0_checked : (List.range' 696320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1360_1_checked : (List.range' 696448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1360_2_checked : (List.range' 696576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1360_3_checked : (List.range' 696704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1360_range (index : Nat) (lower : 696320 ≤ index) (upper : index < 696832) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 696576 then
    if cut : index < 696448 then
      exact segment_sound _ 696320 128 Restriction1360_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 696448 128 Restriction1360_1_checked index (by omega) (by omega)
  else
    if cut : index < 696704 then
      exact segment_sound _ 696576 128 Restriction1360_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 696704 128 Restriction1360_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
