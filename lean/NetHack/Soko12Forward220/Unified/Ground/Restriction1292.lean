import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1292_0_checked : (List.range' 661504 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1292_1_checked : (List.range' 661632 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1292_2_checked : (List.range' 661760 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1292_3_checked : (List.range' 661888 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1292_range (index : Nat) (lower : 661504 ≤ index) (upper : index < 662016) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 661760 then
    if cut : index < 661632 then
      exact segment_sound _ 661504 128 Restriction1292_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 661632 128 Restriction1292_1_checked index (by omega) (by omega)
  else
    if cut : index < 661888 then
      exact segment_sound _ 661760 128 Restriction1292_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 661888 128 Restriction1292_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
