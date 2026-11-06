import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2354_0_checked : (List.range' 1205248 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2354_1_checked : (List.range' 1205376 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2354_2_checked : (List.range' 1205504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2354_3_checked : (List.range' 1205632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2354_range (index : Nat) (lower : 1205248 ≤ index) (upper : index < 1205760) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1205504 then
    if cut : index < 1205376 then
      exact segment_sound _ 1205248 128 Restriction2354_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1205376 128 Restriction2354_1_checked index (by omega) (by omega)
  else
    if cut : index < 1205632 then
      exact segment_sound _ 1205504 128 Restriction2354_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1205632 128 Restriction2354_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
