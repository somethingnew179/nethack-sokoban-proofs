import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2080_0_checked : (List.range' 1064960 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2080_1_checked : (List.range' 1065088 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2080_2_checked : (List.range' 1065216 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2080_3_checked : (List.range' 1065344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2080_range (index : Nat) (lower : 1064960 ≤ index) (upper : index < 1065472) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1065216 then
    if cut : index < 1065088 then
      exact segment_sound _ 1064960 128 Restriction2080_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1065088 128 Restriction2080_1_checked index (by omega) (by omega)
  else
    if cut : index < 1065344 then
      exact segment_sound _ 1065216 128 Restriction2080_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1065344 128 Restriction2080_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
