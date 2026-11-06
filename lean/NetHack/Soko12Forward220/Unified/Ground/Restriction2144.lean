import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2144_0_checked : (List.range' 1097728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2144_1_checked : (List.range' 1097856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2144_2_checked : (List.range' 1097984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2144_3_checked : (List.range' 1098112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2144_range (index : Nat) (lower : 1097728 ≤ index) (upper : index < 1098240) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1097984 then
    if cut : index < 1097856 then
      exact segment_sound _ 1097728 128 Restriction2144_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1097856 128 Restriction2144_1_checked index (by omega) (by omega)
  else
    if cut : index < 1098112 then
      exact segment_sound _ 1097984 128 Restriction2144_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1098112 128 Restriction2144_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
