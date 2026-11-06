import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1922_0_checked : (List.range' 984064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1922_1_checked : (List.range' 984192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1922_2_checked : (List.range' 984320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1922_3_checked : (List.range' 984448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1922_range (index : Nat) (lower : 984064 ≤ index) (upper : index < 984576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 984320 then
    if cut : index < 984192 then
      exact segment_sound _ 984064 128 Restriction1922_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 984192 128 Restriction1922_1_checked index (by omega) (by omega)
  else
    if cut : index < 984448 then
      exact segment_sound _ 984320 128 Restriction1922_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 984448 128 Restriction1922_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
