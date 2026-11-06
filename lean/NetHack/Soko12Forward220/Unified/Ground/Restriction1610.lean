import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1610_0_checked : (List.range' 824320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1610_1_checked : (List.range' 824448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1610_2_checked : (List.range' 824576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1610_3_checked : (List.range' 824704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1610_range (index : Nat) (lower : 824320 ≤ index) (upper : index < 824832) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 824576 then
    if cut : index < 824448 then
      exact segment_sound _ 824320 128 Restriction1610_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 824448 128 Restriction1610_1_checked index (by omega) (by omega)
  else
    if cut : index < 824704 then
      exact segment_sound _ 824576 128 Restriction1610_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 824704 128 Restriction1610_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
