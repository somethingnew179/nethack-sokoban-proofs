import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2430_0_checked : (List.range' 1244160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2430_1_checked : (List.range' 1244288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2430_2_checked : (List.range' 1244416 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2430_3_checked : (List.range' 1244544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2430_range (index : Nat) (lower : 1244160 ≤ index) (upper : index < 1244672) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1244416 then
    if cut : index < 1244288 then
      exact segment_sound _ 1244160 128 Restriction2430_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1244288 128 Restriction2430_1_checked index (by omega) (by omega)
  else
    if cut : index < 1244544 then
      exact segment_sound _ 1244416 128 Restriction2430_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1244544 128 Restriction2430_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
