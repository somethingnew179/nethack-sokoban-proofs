import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1878_0_checked : (List.range' 961536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1878_1_checked : (List.range' 961664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1878_2_checked : (List.range' 961792 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1878_3_checked : (List.range' 961920 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1878_range (index : Nat) (lower : 961536 ≤ index) (upper : index < 962048) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 961792 then
    if cut : index < 961664 then
      exact segment_sound _ 961536 128 Restriction1878_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 961664 128 Restriction1878_1_checked index (by omega) (by omega)
  else
    if cut : index < 961920 then
      exact segment_sound _ 961792 128 Restriction1878_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 961920 128 Restriction1878_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
