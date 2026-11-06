import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1050_0_checked : (List.range' 537600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1050_1_checked : (List.range' 537728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1050_2_checked : (List.range' 537856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1050_3_checked : (List.range' 537984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1050_range (index : Nat) (lower : 537600 ≤ index) (upper : index < 538112) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 537856 then
    if cut : index < 537728 then
      exact segment_sound _ 537600 128 Restriction1050_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 537728 128 Restriction1050_1_checked index (by omega) (by omega)
  else
    if cut : index < 537984 then
      exact segment_sound _ 537856 128 Restriction1050_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 537984 128 Restriction1050_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
