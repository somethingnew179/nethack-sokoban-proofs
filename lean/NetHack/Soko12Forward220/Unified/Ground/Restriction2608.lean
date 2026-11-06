import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2608_0_checked : (List.range' 1335296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2608_1_checked : (List.range' 1335424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2608_2_checked : (List.range' 1335552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2608_3_checked : (List.range' 1335680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2608_range (index : Nat) (lower : 1335296 ≤ index) (upper : index < 1335808) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1335552 then
    if cut : index < 1335424 then
      exact segment_sound _ 1335296 128 Restriction2608_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1335424 128 Restriction2608_1_checked index (by omega) (by omega)
  else
    if cut : index < 1335680 then
      exact segment_sound _ 1335552 128 Restriction2608_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1335680 128 Restriction2608_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
