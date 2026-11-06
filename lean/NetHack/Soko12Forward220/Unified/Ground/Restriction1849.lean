import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1849_0_checked : (List.range' 946688 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1849_1_checked : (List.range' 946816 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1849_2_checked : (List.range' 946944 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1849_3_checked : (List.range' 947072 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1849_range (index : Nat) (lower : 946688 ≤ index) (upper : index < 947200) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 946944 then
    if cut : index < 946816 then
      exact segment_sound _ 946688 128 Restriction1849_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 946816 128 Restriction1849_1_checked index (by omega) (by omega)
  else
    if cut : index < 947072 then
      exact segment_sound _ 946944 128 Restriction1849_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 947072 128 Restriction1849_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
