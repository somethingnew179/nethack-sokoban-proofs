import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2278_0_checked : (List.range' 1166336 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2278_1_checked : (List.range' 1166464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2278_2_checked : (List.range' 1166592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2278_3_checked : (List.range' 1166720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2278_range (index : Nat) (lower : 1166336 ≤ index) (upper : index < 1166848) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1166592 then
    if cut : index < 1166464 then
      exact segment_sound _ 1166336 128 Restriction2278_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1166464 128 Restriction2278_1_checked index (by omega) (by omega)
  else
    if cut : index < 1166720 then
      exact segment_sound _ 1166592 128 Restriction2278_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1166720 128 Restriction2278_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
