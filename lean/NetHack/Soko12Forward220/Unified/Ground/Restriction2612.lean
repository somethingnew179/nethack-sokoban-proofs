import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2612_0_checked : (List.range' 1337344 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2612_1_checked : (List.range' 1337472 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2612_2_checked : (List.range' 1337600 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2612_3_checked : (List.range' 1337728 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2612_range (index : Nat) (lower : 1337344 ≤ index) (upper : index < 1337856) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1337600 then
    if cut : index < 1337472 then
      exact segment_sound _ 1337344 128 Restriction2612_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1337472 128 Restriction2612_1_checked index (by omega) (by omega)
  else
    if cut : index < 1337728 then
      exact segment_sound _ 1337600 128 Restriction2612_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1337728 128 Restriction2612_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
