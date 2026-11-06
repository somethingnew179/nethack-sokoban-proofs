import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2395_0_checked : (List.range' 1226240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2395_1_checked : (List.range' 1226368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2395_2_checked : (List.range' 1226496 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2395_3_checked : (List.range' 1226624 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2395_range (index : Nat) (lower : 1226240 ≤ index) (upper : index < 1226752) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1226496 then
    if cut : index < 1226368 then
      exact segment_sound _ 1226240 128 Restriction2395_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1226368 128 Restriction2395_1_checked index (by omega) (by omega)
  else
    if cut : index < 1226624 then
      exact segment_sound _ 1226496 128 Restriction2395_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1226624 128 Restriction2395_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
