import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1112_0_checked : (List.range' 569344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1112_1_checked : (List.range' 569472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1112_2_checked : (List.range' 569600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1112_3_checked : (List.range' 569728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1112_range (index : Nat) (lower : 569344 ≤ index) (upper : index < 569856) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 569600 then
    if cut : index < 569472 then
      exact segment_sound _ 569344 128 Restriction1112_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 569472 128 Restriction1112_1_checked index (by omega) (by omega)
  else
    if cut : index < 569728 then
      exact segment_sound _ 569600 128 Restriction1112_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 569728 128 Restriction1112_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
