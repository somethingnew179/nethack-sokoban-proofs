import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1162_0_checked : (List.range' 594944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1162_1_checked : (List.range' 595072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1162_2_checked : (List.range' 595200 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1162_3_checked : (List.range' 595328 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1162_range (index : Nat) (lower : 594944 ≤ index) (upper : index < 595456) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 595200 then
    if cut : index < 595072 then
      exact segment_sound _ 594944 128 Restriction1162_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 595072 128 Restriction1162_1_checked index (by omega) (by omega)
  else
    if cut : index < 595328 then
      exact segment_sound _ 595200 128 Restriction1162_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 595328 128 Restriction1162_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
