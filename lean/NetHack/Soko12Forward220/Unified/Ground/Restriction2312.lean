import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2312_0_checked : (List.range' 1183744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2312_1_checked : (List.range' 1183872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2312_2_checked : (List.range' 1184000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2312_3_checked : (List.range' 1184128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2312_range (index : Nat) (lower : 1183744 ≤ index) (upper : index < 1184256) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1184000 then
    if cut : index < 1183872 then
      exact segment_sound _ 1183744 128 Restriction2312_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1183872 128 Restriction2312_1_checked index (by omega) (by omega)
  else
    if cut : index < 1184128 then
      exact segment_sound _ 1184000 128 Restriction2312_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1184128 128 Restriction2312_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
