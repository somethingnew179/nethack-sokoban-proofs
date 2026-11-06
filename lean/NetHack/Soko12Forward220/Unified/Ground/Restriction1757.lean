import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1757_0_checked : (List.range' 899584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1757_1_checked : (List.range' 899712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1757_2_checked : (List.range' 899840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1757_3_checked : (List.range' 899968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1757_range (index : Nat) (lower : 899584 ≤ index) (upper : index < 900096) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 899840 then
    if cut : index < 899712 then
      exact segment_sound _ 899584 128 Restriction1757_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 899712 128 Restriction1757_1_checked index (by omega) (by omega)
  else
    if cut : index < 899968 then
      exact segment_sound _ 899840 128 Restriction1757_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 899968 128 Restriction1757_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
