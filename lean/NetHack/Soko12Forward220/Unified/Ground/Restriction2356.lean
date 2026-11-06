import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2356_0_checked : (List.range' 1206272 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2356_1_checked : (List.range' 1206400 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2356_2_checked : (List.range' 1206528 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2356_3_checked : (List.range' 1206656 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2356_range (index : Nat) (lower : 1206272 ≤ index) (upper : index < 1206784) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1206528 then
    if cut : index < 1206400 then
      exact segment_sound _ 1206272 128 Restriction2356_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1206400 128 Restriction2356_1_checked index (by omega) (by omega)
  else
    if cut : index < 1206656 then
      exact segment_sound _ 1206528 128 Restriction2356_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1206656 128 Restriction2356_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
