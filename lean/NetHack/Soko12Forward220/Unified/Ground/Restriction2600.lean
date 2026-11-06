import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2600_0_checked : (List.range' 1331200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2600_1_checked : (List.range' 1331328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2600_2_checked : (List.range' 1331456 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2600_3_checked : (List.range' 1331584 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2600_range (index : Nat) (lower : 1331200 ≤ index) (upper : index < 1331712) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1331456 then
    if cut : index < 1331328 then
      exact segment_sound _ 1331200 128 Restriction2600_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1331328 128 Restriction2600_1_checked index (by omega) (by omega)
  else
    if cut : index < 1331584 then
      exact segment_sound _ 1331456 128 Restriction2600_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1331584 128 Restriction2600_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
