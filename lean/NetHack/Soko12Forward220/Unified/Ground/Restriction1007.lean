import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1007_0_checked : (List.range' 515584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1007_1_checked : (List.range' 515712 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1007_2_checked : (List.range' 515840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1007_3_checked : (List.range' 515968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1007_range (index : Nat) (lower : 515584 ≤ index) (upper : index < 516096) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 515840 then
    if cut : index < 515712 then
      exact segment_sound _ 515584 128 Restriction1007_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 515712 128 Restriction1007_1_checked index (by omega) (by omega)
  else
    if cut : index < 515968 then
      exact segment_sound _ 515840 128 Restriction1007_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 515968 128 Restriction1007_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
