import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1133_0_checked : (List.range' 580096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1133_1_checked : (List.range' 580224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1133_2_checked : (List.range' 580352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1133_3_checked : (List.range' 580480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1133_range (index : Nat) (lower : 580096 ≤ index) (upper : index < 580608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 580352 then
    if cut : index < 580224 then
      exact segment_sound _ 580096 128 Restriction1133_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 580224 128 Restriction1133_1_checked index (by omega) (by omega)
  else
    if cut : index < 580480 then
      exact segment_sound _ 580352 128 Restriction1133_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 580480 128 Restriction1133_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
