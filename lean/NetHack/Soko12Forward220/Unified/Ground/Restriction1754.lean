import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1754_0_checked : (List.range' 898048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1754_1_checked : (List.range' 898176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1754_2_checked : (List.range' 898304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1754_3_checked : (List.range' 898432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1754_range (index : Nat) (lower : 898048 ≤ index) (upper : index < 898560) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 898304 then
    if cut : index < 898176 then
      exact segment_sound _ 898048 128 Restriction1754_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 898176 128 Restriction1754_1_checked index (by omega) (by omega)
  else
    if cut : index < 898432 then
      exact segment_sound _ 898304 128 Restriction1754_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 898432 128 Restriction1754_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
