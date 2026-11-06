import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2031_0_checked : (List.range' 1039872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2031_1_checked : (List.range' 1040000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2031_2_checked : (List.range' 1040128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2031_3_checked : (List.range' 1040256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2031_range (index : Nat) (lower : 1039872 ≤ index) (upper : index < 1040384) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1040128 then
    if cut : index < 1040000 then
      exact segment_sound _ 1039872 128 Restriction2031_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1040000 128 Restriction2031_1_checked index (by omega) (by omega)
  else
    if cut : index < 1040256 then
      exact segment_sound _ 1040128 128 Restriction2031_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1040256 128 Restriction2031_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
