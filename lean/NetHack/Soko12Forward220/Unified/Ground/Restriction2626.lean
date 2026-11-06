import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2626_0_checked : (List.range' 1344512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2626_1_checked : (List.range' 1344640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2626_2_checked : (List.range' 1344768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2626_3_checked : (List.range' 1344896 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2626_range (index : Nat) (lower : 1344512 ≤ index) (upper : index < 1345024) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1344768 then
    if cut : index < 1344640 then
      exact segment_sound _ 1344512 128 Restriction2626_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1344640 128 Restriction2626_1_checked index (by omega) (by omega)
  else
    if cut : index < 1344896 then
      exact segment_sound _ 1344768 128 Restriction2626_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1344896 128 Restriction2626_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
