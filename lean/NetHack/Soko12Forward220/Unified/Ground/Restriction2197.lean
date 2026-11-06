import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2197_0_checked : (List.range' 1124864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2197_1_checked : (List.range' 1124992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2197_2_checked : (List.range' 1125120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2197_3_checked : (List.range' 1125248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2197_range (index : Nat) (lower : 1124864 ≤ index) (upper : index < 1125376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1125120 then
    if cut : index < 1124992 then
      exact segment_sound _ 1124864 128 Restriction2197_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1124992 128 Restriction2197_1_checked index (by omega) (by omega)
  else
    if cut : index < 1125248 then
      exact segment_sound _ 1125120 128 Restriction2197_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1125248 128 Restriction2197_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
