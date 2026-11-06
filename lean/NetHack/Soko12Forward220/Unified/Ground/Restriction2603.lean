import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2603_0_checked : (List.range' 1332736 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2603_1_checked : (List.range' 1332864 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2603_2_checked : (List.range' 1332992 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2603_3_checked : (List.range' 1333120 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2603_range (index : Nat) (lower : 1332736 ≤ index) (upper : index < 1333248) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1332992 then
    if cut : index < 1332864 then
      exact segment_sound _ 1332736 128 Restriction2603_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1332864 128 Restriction2603_1_checked index (by omega) (by omega)
  else
    if cut : index < 1333120 then
      exact segment_sound _ 1332992 128 Restriction2603_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1333120 128 Restriction2603_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
