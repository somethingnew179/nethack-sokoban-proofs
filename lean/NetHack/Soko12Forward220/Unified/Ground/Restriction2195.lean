import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2195_0_checked : (List.range' 1123840 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2195_1_checked : (List.range' 1123968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2195_2_checked : (List.range' 1124096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2195_3_checked : (List.range' 1124224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2195_range (index : Nat) (lower : 1123840 ≤ index) (upper : index < 1124352) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1124096 then
    if cut : index < 1123968 then
      exact segment_sound _ 1123840 128 Restriction2195_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1123968 128 Restriction2195_1_checked index (by omega) (by omega)
  else
    if cut : index < 1124224 then
      exact segment_sound _ 1124096 128 Restriction2195_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1124224 128 Restriction2195_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
