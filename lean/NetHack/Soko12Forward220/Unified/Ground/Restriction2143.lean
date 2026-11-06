import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2143_0_checked : (List.range' 1097216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2143_1_checked : (List.range' 1097344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2143_2_checked : (List.range' 1097472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2143_3_checked : (List.range' 1097600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2143_range (index : Nat) (lower : 1097216 ≤ index) (upper : index < 1097728) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1097472 then
    if cut : index < 1097344 then
      exact segment_sound _ 1097216 128 Restriction2143_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1097344 128 Restriction2143_1_checked index (by omega) (by omega)
  else
    if cut : index < 1097600 then
      exact segment_sound _ 1097472 128 Restriction2143_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1097600 128 Restriction2143_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
