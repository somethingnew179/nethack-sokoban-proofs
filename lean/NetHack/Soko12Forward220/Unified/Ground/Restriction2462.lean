import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2462_0_checked : (List.range' 1260544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2462_1_checked : (List.range' 1260672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2462_2_checked : (List.range' 1260800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2462_3_checked : (List.range' 1260928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2462_range (index : Nat) (lower : 1260544 ≤ index) (upper : index < 1261056) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1260800 then
    if cut : index < 1260672 then
      exact segment_sound _ 1260544 128 Restriction2462_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1260672 128 Restriction2462_1_checked index (by omega) (by omega)
  else
    if cut : index < 1260928 then
      exact segment_sound _ 1260800 128 Restriction2462_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1260928 128 Restriction2462_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
