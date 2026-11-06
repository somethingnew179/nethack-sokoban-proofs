import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1363_0_checked : (List.range' 697856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1363_1_checked : (List.range' 697984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1363_2_checked : (List.range' 698112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1363_3_checked : (List.range' 698240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1363_range (index : Nat) (lower : 697856 ≤ index) (upper : index < 698368) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 698112 then
    if cut : index < 697984 then
      exact segment_sound _ 697856 128 Restriction1363_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 697984 128 Restriction1363_1_checked index (by omega) (by omega)
  else
    if cut : index < 698240 then
      exact segment_sound _ 698112 128 Restriction1363_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 698240 128 Restriction1363_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
