import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2171_0_checked : (List.range' 1111552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2171_1_checked : (List.range' 1111680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2171_2_checked : (List.range' 1111808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2171_3_checked : (List.range' 1111936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2171_range (index : Nat) (lower : 1111552 ≤ index) (upper : index < 1112064) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1111808 then
    if cut : index < 1111680 then
      exact segment_sound _ 1111552 128 Restriction2171_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1111680 128 Restriction2171_1_checked index (by omega) (by omega)
  else
    if cut : index < 1111936 then
      exact segment_sound _ 1111808 128 Restriction2171_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1111936 128 Restriction2171_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
