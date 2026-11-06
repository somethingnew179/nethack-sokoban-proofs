import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1435_0_checked : (List.range' 734720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1435_1_checked : (List.range' 734848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1435_2_checked : (List.range' 734976 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1435_3_checked : (List.range' 735104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1435_range (index : Nat) (lower : 734720 ≤ index) (upper : index < 735232) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 734976 then
    if cut : index < 734848 then
      exact segment_sound _ 734720 128 Restriction1435_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 734848 128 Restriction1435_1_checked index (by omega) (by omega)
  else
    if cut : index < 735104 then
      exact segment_sound _ 734976 128 Restriction1435_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 735104 128 Restriction1435_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
