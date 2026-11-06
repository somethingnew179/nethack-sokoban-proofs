import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1858_0_checked : (List.range' 951296 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1858_1_checked : (List.range' 951424 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1858_2_checked : (List.range' 951552 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1858_3_checked : (List.range' 951680 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1858_range (index : Nat) (lower : 951296 ≤ index) (upper : index < 951808) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 951552 then
    if cut : index < 951424 then
      exact segment_sound _ 951296 128 Restriction1858_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 951424 128 Restriction1858_1_checked index (by omega) (by omega)
  else
    if cut : index < 951680 then
      exact segment_sound _ 951552 128 Restriction1858_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 951680 128 Restriction1858_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
