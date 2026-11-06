import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2431_0_checked : (List.range' 1244672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2431_1_checked : (List.range' 1244800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2431_2_checked : (List.range' 1244928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2431_3_checked : (List.range' 1245056 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2431_range (index : Nat) (lower : 1244672 ≤ index) (upper : index < 1245184) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1244928 then
    if cut : index < 1244800 then
      exact segment_sound _ 1244672 128 Restriction2431_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1244800 128 Restriction2431_1_checked index (by omega) (by omega)
  else
    if cut : index < 1245056 then
      exact segment_sound _ 1244928 128 Restriction2431_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1245056 128 Restriction2431_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
