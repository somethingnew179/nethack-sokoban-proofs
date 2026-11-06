import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2169_0_checked : (List.range' 1110528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2169_1_checked : (List.range' 1110656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2169_2_checked : (List.range' 1110784 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2169_3_checked : (List.range' 1110912 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2169_range (index : Nat) (lower : 1110528 ≤ index) (upper : index < 1111040) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1110784 then
    if cut : index < 1110656 then
      exact segment_sound _ 1110528 128 Restriction2169_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1110656 128 Restriction2169_1_checked index (by omega) (by omega)
  else
    if cut : index < 1110912 then
      exact segment_sound _ 1110784 128 Restriction2169_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1110912 128 Restriction2169_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
