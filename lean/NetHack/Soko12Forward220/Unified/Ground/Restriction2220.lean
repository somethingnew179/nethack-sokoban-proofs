import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2220_0_checked : (List.range' 1136640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2220_1_checked : (List.range' 1136768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2220_2_checked : (List.range' 1136896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2220_3_checked : (List.range' 1137024 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2220_range (index : Nat) (lower : 1136640 ≤ index) (upper : index < 1137152) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1136896 then
    if cut : index < 1136768 then
      exact segment_sound _ 1136640 128 Restriction2220_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1136768 128 Restriction2220_1_checked index (by omega) (by omega)
  else
    if cut : index < 1137024 then
      exact segment_sound _ 1136896 128 Restriction2220_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1137024 128 Restriction2220_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
