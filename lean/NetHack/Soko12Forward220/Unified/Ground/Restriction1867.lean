import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1867_0_checked : (List.range' 955904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1867_1_checked : (List.range' 956032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1867_2_checked : (List.range' 956160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1867_3_checked : (List.range' 956288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1867_range (index : Nat) (lower : 955904 ≤ index) (upper : index < 956416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 956160 then
    if cut : index < 956032 then
      exact segment_sound _ 955904 128 Restriction1867_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 956032 128 Restriction1867_1_checked index (by omega) (by omega)
  else
    if cut : index < 956288 then
      exact segment_sound _ 956160 128 Restriction1867_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 956288 128 Restriction1867_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
