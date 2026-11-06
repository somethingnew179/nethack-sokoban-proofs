import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1737_0_checked : (List.range' 889344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1737_1_checked : (List.range' 889472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1737_2_checked : (List.range' 889600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1737_3_checked : (List.range' 889728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1737_range (index : Nat) (lower : 889344 ≤ index) (upper : index < 889856) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 889600 then
    if cut : index < 889472 then
      exact segment_sound _ 889344 128 Restriction1737_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 889472 128 Restriction1737_1_checked index (by omega) (by omega)
  else
    if cut : index < 889728 then
      exact segment_sound _ 889600 128 Restriction1737_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 889728 128 Restriction1737_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
