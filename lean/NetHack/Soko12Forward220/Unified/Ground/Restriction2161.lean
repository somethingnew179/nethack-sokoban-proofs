import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2161_0_checked : (List.range' 1106432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2161_1_checked : (List.range' 1106560 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2161_2_checked : (List.range' 1106688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2161_3_checked : (List.range' 1106816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2161_range (index : Nat) (lower : 1106432 ≤ index) (upper : index < 1106944) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1106688 then
    if cut : index < 1106560 then
      exact segment_sound _ 1106432 128 Restriction2161_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1106560 128 Restriction2161_1_checked index (by omega) (by omega)
  else
    if cut : index < 1106816 then
      exact segment_sound _ 1106688 128 Restriction2161_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1106816 128 Restriction2161_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
