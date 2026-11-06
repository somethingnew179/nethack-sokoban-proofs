import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1164_0_checked : (List.range' 595968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1164_1_checked : (List.range' 596096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1164_2_checked : (List.range' 596224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1164_3_checked : (List.range' 596352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1164_range (index : Nat) (lower : 595968 ≤ index) (upper : index < 596480) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 596224 then
    if cut : index < 596096 then
      exact segment_sound _ 595968 128 Restriction1164_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 596096 128 Restriction1164_1_checked index (by omega) (by omega)
  else
    if cut : index < 596352 then
      exact segment_sound _ 596224 128 Restriction1164_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 596352 128 Restriction1164_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
