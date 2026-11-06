import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1630_0_checked : (List.range' 834560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1630_1_checked : (List.range' 834688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1630_2_checked : (List.range' 834816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1630_3_checked : (List.range' 834944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1630_range (index : Nat) (lower : 834560 ≤ index) (upper : index < 835072) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 834816 then
    if cut : index < 834688 then
      exact segment_sound _ 834560 128 Restriction1630_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 834688 128 Restriction1630_1_checked index (by omega) (by omega)
  else
    if cut : index < 834944 then
      exact segment_sound _ 834816 128 Restriction1630_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 834944 128 Restriction1630_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
