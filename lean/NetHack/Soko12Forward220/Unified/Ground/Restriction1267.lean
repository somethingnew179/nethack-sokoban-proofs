import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1267_0_checked : (List.range' 648704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1267_1_checked : (List.range' 648832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1267_2_checked : (List.range' 648960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1267_3_checked : (List.range' 649088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1267_range (index : Nat) (lower : 648704 ≤ index) (upper : index < 649216) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 648960 then
    if cut : index < 648832 then
      exact segment_sound _ 648704 128 Restriction1267_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 648832 128 Restriction1267_1_checked index (by omega) (by omega)
  else
    if cut : index < 649088 then
      exact segment_sound _ 648960 128 Restriction1267_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 649088 128 Restriction1267_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
