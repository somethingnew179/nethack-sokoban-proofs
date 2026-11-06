import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2392_0_checked : (List.range' 1224704 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2392_1_checked : (List.range' 1224832 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2392_2_checked : (List.range' 1224960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2392_3_checked : (List.range' 1225088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2392_range (index : Nat) (lower : 1224704 ≤ index) (upper : index < 1225216) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1224960 then
    if cut : index < 1224832 then
      exact segment_sound _ 1224704 128 Restriction2392_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1224832 128 Restriction2392_1_checked index (by omega) (by omega)
  else
    if cut : index < 1225088 then
      exact segment_sound _ 1224960 128 Restriction2392_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1225088 128 Restriction2392_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
