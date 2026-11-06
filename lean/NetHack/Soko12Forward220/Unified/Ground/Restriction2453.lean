import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2453_0_checked : (List.range' 1255936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2453_1_checked : (List.range' 1256064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2453_2_checked : (List.range' 1256192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2453_3_checked : (List.range' 1256320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2453_range (index : Nat) (lower : 1255936 ≤ index) (upper : index < 1256448) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1256192 then
    if cut : index < 1256064 then
      exact segment_sound _ 1255936 128 Restriction2453_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1256064 128 Restriction2453_1_checked index (by omega) (by omega)
  else
    if cut : index < 1256320 then
      exact segment_sound _ 1256192 128 Restriction2453_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1256320 128 Restriction2453_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
