import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1774_0_checked : (List.range' 908288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1774_1_checked : (List.range' 908416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1774_2_checked : (List.range' 908544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1774_3_checked : (List.range' 908672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1774_range (index : Nat) (lower : 908288 ≤ index) (upper : index < 908800) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 908544 then
    if cut : index < 908416 then
      exact segment_sound _ 908288 128 Restriction1774_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 908416 128 Restriction1774_1_checked index (by omega) (by omega)
  else
    if cut : index < 908672 then
      exact segment_sound _ 908544 128 Restriction1774_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 908672 128 Restriction1774_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
