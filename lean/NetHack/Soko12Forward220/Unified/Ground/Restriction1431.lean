import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1431_0_checked : (List.range' 732672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1431_1_checked : (List.range' 732800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1431_2_checked : (List.range' 732928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1431_3_checked : (List.range' 733056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1431_range (index : Nat) (lower : 732672 ≤ index) (upper : index < 733184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 732928 then
    if cut : index < 732800 then
      exact segment_sound _ 732672 128 Restriction1431_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 732800 128 Restriction1431_1_checked index (by omega) (by omega)
  else
    if cut : index < 733056 then
      exact segment_sound _ 732928 128 Restriction1431_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 733056 128 Restriction1431_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
