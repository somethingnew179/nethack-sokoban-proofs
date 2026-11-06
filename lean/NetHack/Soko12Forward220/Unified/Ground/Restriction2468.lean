import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2468_0_checked : (List.range' 1263616 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2468_1_checked : (List.range' 1263744 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2468_2_checked : (List.range' 1263872 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2468_3_checked : (List.range' 1264000 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2468_range (index : Nat) (lower : 1263616 ≤ index) (upper : index < 1264128) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1263872 then
    if cut : index < 1263744 then
      exact segment_sound _ 1263616 128 Restriction2468_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1263744 128 Restriction2468_1_checked index (by omega) (by omega)
  else
    if cut : index < 1264000 then
      exact segment_sound _ 1263872 128 Restriction2468_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1264000 128 Restriction2468_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
