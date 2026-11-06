import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2390_0_checked : (List.range' 1223680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2390_1_checked : (List.range' 1223808 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2390_2_checked : (List.range' 1223936 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2390_3_checked : (List.range' 1224064 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2390_range (index : Nat) (lower : 1223680 ≤ index) (upper : index < 1224192) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1223936 then
    if cut : index < 1223808 then
      exact segment_sound _ 1223680 128 Restriction2390_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1223808 128 Restriction2390_1_checked index (by omega) (by omega)
  else
    if cut : index < 1224064 then
      exact segment_sound _ 1223936 128 Restriction2390_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1224064 128 Restriction2390_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
