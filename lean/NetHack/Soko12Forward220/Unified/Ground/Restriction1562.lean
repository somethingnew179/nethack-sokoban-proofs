import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1562_0_checked : (List.range' 799744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1562_1_checked : (List.range' 799872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1562_2_checked : (List.range' 800000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1562_3_checked : (List.range' 800128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1562_range (index : Nat) (lower : 799744 ≤ index) (upper : index < 800256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 800000 then
    if cut : index < 799872 then
      exact segment_sound _ 799744 128 Restriction1562_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 799872 128 Restriction1562_1_checked index (by omega) (by omega)
  else
    if cut : index < 800128 then
      exact segment_sound _ 800000 128 Restriction1562_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 800128 128 Restriction1562_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
