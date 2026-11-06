import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2450_0_checked : (List.range' 1254400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2450_1_checked : (List.range' 1254528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2450_2_checked : (List.range' 1254656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2450_3_checked : (List.range' 1254784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2450_range (index : Nat) (lower : 1254400 ≤ index) (upper : index < 1254912) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1254656 then
    if cut : index < 1254528 then
      exact segment_sound _ 1254400 128 Restriction2450_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1254528 128 Restriction2450_1_checked index (by omega) (by omega)
  else
    if cut : index < 1254784 then
      exact segment_sound _ 1254656 128 Restriction2450_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1254784 128 Restriction2450_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
