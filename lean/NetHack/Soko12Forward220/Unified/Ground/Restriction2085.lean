import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2085_0_checked : (List.range' 1067520 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2085_1_checked : (List.range' 1067648 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2085_2_checked : (List.range' 1067776 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2085_3_checked : (List.range' 1067904 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2085_range (index : Nat) (lower : 1067520 ≤ index) (upper : index < 1068032) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1067776 then
    if cut : index < 1067648 then
      exact segment_sound _ 1067520 128 Restriction2085_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1067648 128 Restriction2085_1_checked index (by omega) (by omega)
  else
    if cut : index < 1067904 then
      exact segment_sound _ 1067776 128 Restriction2085_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1067904 128 Restriction2085_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
