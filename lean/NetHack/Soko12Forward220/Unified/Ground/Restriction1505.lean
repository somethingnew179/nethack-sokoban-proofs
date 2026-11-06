import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1505_0_checked : (List.range' 770560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1505_1_checked : (List.range' 770688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1505_2_checked : (List.range' 770816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1505_3_checked : (List.range' 770944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1505_range (index : Nat) (lower : 770560 ≤ index) (upper : index < 771072) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 770816 then
    if cut : index < 770688 then
      exact segment_sound _ 770560 128 Restriction1505_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 770688 128 Restriction1505_1_checked index (by omega) (by omega)
  else
    if cut : index < 770944 then
      exact segment_sound _ 770816 128 Restriction1505_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 770944 128 Restriction1505_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
