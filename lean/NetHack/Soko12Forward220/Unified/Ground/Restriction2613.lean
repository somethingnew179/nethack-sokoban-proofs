import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2613_0_checked : (List.range' 1337856 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2613_1_checked : (List.range' 1337984 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2613_2_checked : (List.range' 1338112 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2613_3_checked : (List.range' 1338240 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2613_range (index : Nat) (lower : 1337856 ≤ index) (upper : index < 1338368) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1338112 then
    if cut : index < 1337984 then
      exact segment_sound _ 1337856 128 Restriction2613_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1337984 128 Restriction2613_1_checked index (by omega) (by omega)
  else
    if cut : index < 1338240 then
      exact segment_sound _ 1338112 128 Restriction2613_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1338240 128 Restriction2613_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
