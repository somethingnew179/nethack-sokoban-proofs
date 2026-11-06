import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1877_0_checked : (List.range' 961024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1877_1_checked : (List.range' 961152 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1877_2_checked : (List.range' 961280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1877_3_checked : (List.range' 961408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1877_range (index : Nat) (lower : 961024 ≤ index) (upper : index < 961536) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 961280 then
    if cut : index < 961152 then
      exact segment_sound _ 961024 128 Restriction1877_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 961152 128 Restriction1877_1_checked index (by omega) (by omega)
  else
    if cut : index < 961408 then
      exact segment_sound _ 961280 128 Restriction1877_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 961408 128 Restriction1877_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
