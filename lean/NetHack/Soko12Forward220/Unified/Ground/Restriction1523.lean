import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1523_0_checked : (List.range' 779776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1523_1_checked : (List.range' 779904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1523_2_checked : (List.range' 780032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1523_3_checked : (List.range' 780160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1523_range (index : Nat) (lower : 779776 ≤ index) (upper : index < 780288) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 780032 then
    if cut : index < 779904 then
      exact segment_sound _ 779776 128 Restriction1523_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 779904 128 Restriction1523_1_checked index (by omega) (by omega)
  else
    if cut : index < 780160 then
      exact segment_sound _ 780032 128 Restriction1523_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 780160 128 Restriction1523_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
