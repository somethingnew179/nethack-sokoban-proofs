import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2322_0_checked : (List.range' 1188864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2322_1_checked : (List.range' 1188992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2322_2_checked : (List.range' 1189120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2322_3_checked : (List.range' 1189248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2322_range (index : Nat) (lower : 1188864 ≤ index) (upper : index < 1189376) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1189120 then
    if cut : index < 1188992 then
      exact segment_sound _ 1188864 128 Restriction2322_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1188992 128 Restriction2322_1_checked index (by omega) (by omega)
  else
    if cut : index < 1189248 then
      exact segment_sound _ 1189120 128 Restriction2322_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1189248 128 Restriction2322_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
