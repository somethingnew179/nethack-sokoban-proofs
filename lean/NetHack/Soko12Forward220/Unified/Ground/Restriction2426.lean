import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2426_0_checked : (List.range' 1242112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2426_1_checked : (List.range' 1242240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2426_2_checked : (List.range' 1242368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2426_3_checked : (List.range' 1242496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2426_range (index : Nat) (lower : 1242112 ≤ index) (upper : index < 1242624) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1242368 then
    if cut : index < 1242240 then
      exact segment_sound _ 1242112 128 Restriction2426_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1242240 128 Restriction2426_1_checked index (by omega) (by omega)
  else
    if cut : index < 1242496 then
      exact segment_sound _ 1242368 128 Restriction2426_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1242496 128 Restriction2426_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
