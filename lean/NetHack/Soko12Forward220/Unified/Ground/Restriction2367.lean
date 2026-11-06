import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2367_0_checked : (List.range' 1211904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2367_1_checked : (List.range' 1212032 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2367_2_checked : (List.range' 1212160 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2367_3_checked : (List.range' 1212288 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2367_range (index : Nat) (lower : 1211904 ≤ index) (upper : index < 1212416) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1212160 then
    if cut : index < 1212032 then
      exact segment_sound _ 1211904 128 Restriction2367_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1212032 128 Restriction2367_1_checked index (by omega) (by omega)
  else
    if cut : index < 1212288 then
      exact segment_sound _ 1212160 128 Restriction2367_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1212288 128 Restriction2367_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
