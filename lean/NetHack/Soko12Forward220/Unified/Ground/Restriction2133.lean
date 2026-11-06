import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2133_0_checked : (List.range' 1092096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2133_1_checked : (List.range' 1092224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2133_2_checked : (List.range' 1092352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2133_3_checked : (List.range' 1092480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2133_range (index : Nat) (lower : 1092096 ≤ index) (upper : index < 1092608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1092352 then
    if cut : index < 1092224 then
      exact segment_sound _ 1092096 128 Restriction2133_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1092224 128 Restriction2133_1_checked index (by omega) (by omega)
  else
    if cut : index < 1092480 then
      exact segment_sound _ 1092352 128 Restriction2133_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1092480 128 Restriction2133_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
