import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2447_0_checked : (List.range' 1252864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2447_1_checked : (List.range' 1252992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2447_2_checked : (List.range' 1253120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2447_3_checked : (List.range' 1253248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2447_range (index : Nat) (lower : 1252864 ≤ index) (upper : index < 1253376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1253120 then
    if cut : index < 1252992 then
      exact segment_sound _ 1252864 128 Restriction2447_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1252992 128 Restriction2447_1_checked index (by omega) (by omega)
  else
    if cut : index < 1253248 then
      exact segment_sound _ 1253120 128 Restriction2447_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1253248 128 Restriction2447_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
