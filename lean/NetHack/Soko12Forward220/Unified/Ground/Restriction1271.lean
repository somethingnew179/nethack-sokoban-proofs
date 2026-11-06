import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1271_0_checked : (List.range' 650752 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1271_1_checked : (List.range' 650880 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1271_2_checked : (List.range' 651008 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1271_3_checked : (List.range' 651136 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1271_range (index : Nat) (lower : 650752 ≤ index) (upper : index < 651264) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 651008 then
    if cut : index < 650880 then
      exact segment_sound _ 650752 128 Restriction1271_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 650880 128 Restriction1271_1_checked index (by omega) (by omega)
  else
    if cut : index < 651136 then
      exact segment_sound _ 651008 128 Restriction1271_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 651136 128 Restriction1271_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
