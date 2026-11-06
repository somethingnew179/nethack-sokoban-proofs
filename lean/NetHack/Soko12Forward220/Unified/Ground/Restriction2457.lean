import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2457_0_checked : (List.range' 1257984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2457_1_checked : (List.range' 1258112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2457_2_checked : (List.range' 1258240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2457_3_checked : (List.range' 1258368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2457_range (index : Nat) (lower : 1257984 ≤ index) (upper : index < 1258496) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1258240 then
    if cut : index < 1258112 then
      exact segment_sound _ 1257984 128 Restriction2457_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1258112 128 Restriction2457_1_checked index (by omega) (by omega)
  else
    if cut : index < 1258368 then
      exact segment_sound _ 1258240 128 Restriction2457_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1258368 128 Restriction2457_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
