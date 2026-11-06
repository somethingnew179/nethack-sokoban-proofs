import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2602_0_checked : (List.range' 1332224 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2602_1_checked : (List.range' 1332352 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2602_2_checked : (List.range' 1332480 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2602_3_checked : (List.range' 1332608 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2602_range (index : Nat) (lower : 1332224 ≤ index) (upper : index < 1332736) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1332480 then
    if cut : index < 1332352 then
      exact segment_sound _ 1332224 128 Restriction2602_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1332352 128 Restriction2602_1_checked index (by omega) (by omega)
  else
    if cut : index < 1332608 then
      exact segment_sound _ 1332480 128 Restriction2602_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1332608 128 Restriction2602_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
