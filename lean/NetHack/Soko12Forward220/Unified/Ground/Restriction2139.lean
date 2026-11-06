import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2139_0_checked : (List.range' 1095168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2139_1_checked : (List.range' 1095296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2139_2_checked : (List.range' 1095424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2139_3_checked : (List.range' 1095552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2139_range (index : Nat) (lower : 1095168 ≤ index) (upper : index < 1095680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1095424 then
    if cut : index < 1095296 then
      exact segment_sound _ 1095168 128 Restriction2139_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1095296 128 Restriction2139_1_checked index (by omega) (by omega)
  else
    if cut : index < 1095552 then
      exact segment_sound _ 1095424 128 Restriction2139_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1095552 128 Restriction2139_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
