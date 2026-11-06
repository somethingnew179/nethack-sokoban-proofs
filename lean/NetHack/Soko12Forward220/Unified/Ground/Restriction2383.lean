import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2383_0_checked : (List.range' 1220096 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2383_1_checked : (List.range' 1220224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2383_2_checked : (List.range' 1220352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2383_3_checked : (List.range' 1220480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2383_range (index : Nat) (lower : 1220096 ≤ index) (upper : index < 1220608) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1220352 then
    if cut : index < 1220224 then
      exact segment_sound _ 1220096 128 Restriction2383_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1220224 128 Restriction2383_1_checked index (by omega) (by omega)
  else
    if cut : index < 1220480 then
      exact segment_sound _ 1220352 128 Restriction2383_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1220480 128 Restriction2383_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
