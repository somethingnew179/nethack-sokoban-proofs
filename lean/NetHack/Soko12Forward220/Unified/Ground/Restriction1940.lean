import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1940_0_checked : (List.range' 993280 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1940_1_checked : (List.range' 993408 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1940_2_checked : (List.range' 993536 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1940_3_checked : (List.range' 993664 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1940_range (index : Nat) (lower : 993280 ≤ index) (upper : index < 993792) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 993536 then
    if cut : index < 993408 then
      exact segment_sound _ 993280 128 Restriction1940_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 993408 128 Restriction1940_1_checked index (by omega) (by omega)
  else
    if cut : index < 993664 then
      exact segment_sound _ 993536 128 Restriction1940_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 993664 128 Restriction1940_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
