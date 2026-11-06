import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0457_0_checked : (List.range' 233984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0457_1_checked : (List.range' 234112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0457_2_checked : (List.range' 234240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0457_3_checked : (List.range' 234368 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0457_range (index : Nat) (lower : 233984 ≤ index) (upper : index < 234496) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 234240 then
    if cut : index < 234112 then
      exact segment_sound _ 233984 128 Restriction0457_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 234112 128 Restriction0457_1_checked index (by omega) (by omega)
  else
    if cut : index < 234368 then
      exact segment_sound _ 234240 128 Restriction0457_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 234368 128 Restriction0457_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
