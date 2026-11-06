import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1003_0_checked : (List.range' 513536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1003_1_checked : (List.range' 513664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1003_2_checked : (List.range' 513792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1003_3_checked : (List.range' 513920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1003_range (index : Nat) (lower : 513536 ≤ index) (upper : index < 514048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 513792 then
    if cut : index < 513664 then
      exact segment_sound _ 513536 128 Restriction1003_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 513664 128 Restriction1003_1_checked index (by omega) (by omega)
  else
    if cut : index < 513920 then
      exact segment_sound _ 513792 128 Restriction1003_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 513920 128 Restriction1003_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
