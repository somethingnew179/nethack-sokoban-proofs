import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2469_0_checked : (List.range' 1264128 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2469_1_checked : (List.range' 1264256 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2469_2_checked : (List.range' 1264384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2469_3_checked : (List.range' 1264512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2469_range (index : Nat) (lower : 1264128 ≤ index) (upper : index < 1264640) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1264384 then
    if cut : index < 1264256 then
      exact segment_sound _ 1264128 128 Restriction2469_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1264256 128 Restriction2469_1_checked index (by omega) (by omega)
  else
    if cut : index < 1264512 then
      exact segment_sound _ 1264384 128 Restriction2469_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1264512 128 Restriction2469_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
