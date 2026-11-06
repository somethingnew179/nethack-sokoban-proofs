import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction1863_0_checked : (List.range' 953856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1863_1_checked : (List.range' 953984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1863_2_checked : (List.range' 954112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1863_3_checked : (List.range' 954240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction1863_range (index : Nat) (lower : 953856 ≤ index) (upper : index < 954368) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 954112 then
    if cut : index < 953984 then
      exact segment_sound _ 953856 128 Restriction1863_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 953984 128 Restriction1863_1_checked index (by omega) (by omega)
  else
    if cut : index < 954240 then
      exact segment_sound _ 954112 128 Restriction1863_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 954240 128 Restriction1863_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
