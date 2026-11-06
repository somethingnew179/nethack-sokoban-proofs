import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2206_0_checked : (List.range' 1129472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2206_1_checked : (List.range' 1129600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2206_2_checked : (List.range' 1129728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2206_3_checked : (List.range' 1129856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2206_range (index : Nat) (lower : 1129472 ≤ index) (upper : index < 1129984) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1129728 then
    if cut : index < 1129600 then
      exact segment_sound _ 1129472 128 Restriction2206_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1129600 128 Restriction2206_1_checked index (by omega) (by omega)
  else
    if cut : index < 1129856 then
      exact segment_sound _ 1129728 128 Restriction2206_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1129856 128 Restriction2206_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
