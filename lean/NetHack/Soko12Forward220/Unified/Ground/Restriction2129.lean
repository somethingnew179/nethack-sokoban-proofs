import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2129_0_checked : (List.range' 1090048 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2129_1_checked : (List.range' 1090176 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2129_2_checked : (List.range' 1090304 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2129_3_checked : (List.range' 1090432 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2129_range (index : Nat) (lower : 1090048 ≤ index) (upper : index < 1090560) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1090304 then
    if cut : index < 1090176 then
      exact segment_sound _ 1090048 128 Restriction2129_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1090176 128 Restriction2129_1_checked index (by omega) (by omega)
  else
    if cut : index < 1090432 then
      exact segment_sound _ 1090304 128 Restriction2129_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1090432 128 Restriction2129_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
