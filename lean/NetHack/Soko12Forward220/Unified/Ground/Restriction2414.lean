import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2414_0_checked : (List.range' 1235968 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2414_1_checked : (List.range' 1236096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2414_2_checked : (List.range' 1236224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2414_3_checked : (List.range' 1236352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2414_range (index : Nat) (lower : 1235968 ≤ index) (upper : index < 1236480) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1236224 then
    if cut : index < 1236096 then
      exact segment_sound _ 1235968 128 Restriction2414_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1236096 128 Restriction2414_1_checked index (by omega) (by omega)
  else
    if cut : index < 1236352 then
      exact segment_sound _ 1236224 128 Restriction2414_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1236352 128 Restriction2414_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
