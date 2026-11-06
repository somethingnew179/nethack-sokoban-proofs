import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2579_0_checked : (List.range' 1320448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2579_1_checked : (List.range' 1320576 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2579_2_checked : (List.range' 1320704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2579_3_checked : (List.range' 1320832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2579_range (index : Nat) (lower : 1320448 ≤ index) (upper : index < 1320960) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1320704 then
    if cut : index < 1320576 then
      exact segment_sound _ 1320448 128 Restriction2579_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1320576 128 Restriction2579_1_checked index (by omega) (by omega)
  else
    if cut : index < 1320832 then
      exact segment_sound _ 1320704 128 Restriction2579_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1320832 128 Restriction2579_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
