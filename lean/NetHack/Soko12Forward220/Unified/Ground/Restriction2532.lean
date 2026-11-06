import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2532_0_checked : (List.range' 1296384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2532_1_checked : (List.range' 1296512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2532_2_checked : (List.range' 1296640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2532_3_checked : (List.range' 1296768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2532_range (index : Nat) (lower : 1296384 ≤ index) (upper : index < 1296896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1296640 then
    if cut : index < 1296512 then
      exact segment_sound _ 1296384 128 Restriction2532_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1296512 128 Restriction2532_1_checked index (by omega) (by omega)
  else
    if cut : index < 1296768 then
      exact segment_sound _ 1296640 128 Restriction2532_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1296768 128 Restriction2532_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
