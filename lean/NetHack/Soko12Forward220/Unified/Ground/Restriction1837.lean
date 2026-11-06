import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1837_0_checked : (List.range' 940544 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1837_1_checked : (List.range' 940672 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1837_2_checked : (List.range' 940800 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1837_3_checked : (List.range' 940928 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1837_range (index : Nat) (lower : 940544 ≤ index) (upper : index < 941056) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 940800 then
    if cut : index < 940672 then
      exact segment_sound _ 940544 128 Restriction1837_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 940672 128 Restriction1837_1_checked index (by omega) (by omega)
  else
    if cut : index < 940928 then
      exact segment_sound _ 940800 128 Restriction1837_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 940928 128 Restriction1837_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
