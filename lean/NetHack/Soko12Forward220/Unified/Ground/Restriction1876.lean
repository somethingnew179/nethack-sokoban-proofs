import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1876_0_checked : (List.range' 960512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1876_1_checked : (List.range' 960640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1876_2_checked : (List.range' 960768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1876_3_checked : (List.range' 960896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1876_range (index : Nat) (lower : 960512 ≤ index) (upper : index < 961024) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 960768 then
    if cut : index < 960640 then
      exact segment_sound _ 960512 128 Restriction1876_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 960640 128 Restriction1876_1_checked index (by omega) (by omega)
  else
    if cut : index < 960896 then
      exact segment_sound _ 960768 128 Restriction1876_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 960896 128 Restriction1876_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
