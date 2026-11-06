import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1514_0_checked : (List.range' 775168 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1514_1_checked : (List.range' 775296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1514_2_checked : (List.range' 775424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1514_3_checked : (List.range' 775552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1514_range (index : Nat) (lower : 775168 ≤ index) (upper : index < 775680) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 775424 then
    if cut : index < 775296 then
      exact segment_sound _ 775168 128 Restriction1514_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 775296 128 Restriction1514_1_checked index (by omega) (by omega)
  else
    if cut : index < 775552 then
      exact segment_sound _ 775424 128 Restriction1514_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 775552 128 Restriction1514_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
