import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1842_0_checked : (List.range' 943104 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1842_1_checked : (List.range' 943232 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1842_2_checked : (List.range' 943360 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1842_3_checked : (List.range' 943488 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1842_range (index : Nat) (lower : 943104 ≤ index) (upper : index < 943616) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 943360 then
    if cut : index < 943232 then
      exact segment_sound _ 943104 128 Restriction1842_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 943232 128 Restriction1842_1_checked index (by omega) (by omega)
  else
    if cut : index < 943488 then
      exact segment_sound _ 943360 128 Restriction1842_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 943488 128 Restriction1842_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
