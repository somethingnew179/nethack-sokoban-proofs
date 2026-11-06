import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1108_0_checked : (List.range' 567296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1108_1_checked : (List.range' 567424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1108_2_checked : (List.range' 567552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1108_3_checked : (List.range' 567680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1108_range (index : Nat) (lower : 567296 ≤ index) (upper : index < 567808) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 567552 then
    if cut : index < 567424 then
      exact segment_sound _ 567296 128 Restriction1108_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 567424 128 Restriction1108_1_checked index (by omega) (by omega)
  else
    if cut : index < 567680 then
      exact segment_sound _ 567552 128 Restriction1108_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 567680 128 Restriction1108_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
