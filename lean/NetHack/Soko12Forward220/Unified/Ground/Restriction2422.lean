import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2422_0_checked : (List.range' 1240064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2422_1_checked : (List.range' 1240192 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2422_2_checked : (List.range' 1240320 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2422_3_checked : (List.range' 1240448 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2422_range (index : Nat) (lower : 1240064 ≤ index) (upper : index < 1240576) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1240320 then
    if cut : index < 1240192 then
      exact segment_sound _ 1240064 128 Restriction2422_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1240192 128 Restriction2422_1_checked index (by omega) (by omega)
  else
    if cut : index < 1240448 then
      exact segment_sound _ 1240320 128 Restriction2422_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1240448 128 Restriction2422_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
