import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2174_0_checked : (List.range' 1113088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2174_1_checked : (List.range' 1113216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2174_2_checked : (List.range' 1113344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2174_3_checked : (List.range' 1113472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2174_range (index : Nat) (lower : 1113088 ≤ index) (upper : index < 1113600) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1113344 then
    if cut : index < 1113216 then
      exact segment_sound _ 1113088 128 Restriction2174_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1113216 128 Restriction2174_1_checked index (by omega) (by omega)
  else
    if cut : index < 1113472 then
      exact segment_sound _ 1113344 128 Restriction2174_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1113472 128 Restriction2174_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
