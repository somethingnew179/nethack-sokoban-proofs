import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1564_0_checked : (List.range' 800768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1564_1_checked : (List.range' 800896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1564_2_checked : (List.range' 801024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1564_3_checked : (List.range' 801152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1564_range (index : Nat) (lower : 800768 ≤ index) (upper : index < 801280) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 801024 then
    if cut : index < 800896 then
      exact segment_sound _ 800768 128 Restriction1564_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 800896 128 Restriction1564_1_checked index (by omega) (by omega)
  else
    if cut : index < 801152 then
      exact segment_sound _ 801024 128 Restriction1564_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 801152 128 Restriction1564_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
