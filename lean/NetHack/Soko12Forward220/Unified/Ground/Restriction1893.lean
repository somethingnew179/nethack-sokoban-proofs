import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1893_0_checked : (List.range' 969216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1893_1_checked : (List.range' 969344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1893_2_checked : (List.range' 969472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1893_3_checked : (List.range' 969600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1893_range (index : Nat) (lower : 969216 ≤ index) (upper : index < 969728) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 969472 then
    if cut : index < 969344 then
      exact segment_sound _ 969216 128 Restriction1893_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 969344 128 Restriction1893_1_checked index (by omega) (by omega)
  else
    if cut : index < 969600 then
      exact segment_sound _ 969472 128 Restriction1893_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 969600 128 Restriction1893_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
