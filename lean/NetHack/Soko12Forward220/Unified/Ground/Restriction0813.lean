import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0813_0_checked : (List.range' 416256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0813_1_checked : (List.range' 416384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0813_2_checked : (List.range' 416512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0813_3_checked : (List.range' 416640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0813_range (index : Nat) (lower : 416256 ≤ index) (upper : index < 416768) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 416512 then
    if cut : index < 416384 then
      exact segment_sound _ 416256 128 Restriction0813_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 416384 128 Restriction0813_1_checked index (by omega) (by omega)
  else
    if cut : index < 416640 then
      exact segment_sound _ 416512 128 Restriction0813_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 416640 128 Restriction0813_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
