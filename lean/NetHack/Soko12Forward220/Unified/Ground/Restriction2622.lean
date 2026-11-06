import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction2622_0_checked : (List.range' 1342464 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2622_1_checked : (List.range' 1342592 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2622_2_checked : (List.range' 1342720 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2622_3_checked : (List.range' 1342848 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction2622_range (index : Nat) (lower : 1342464 ≤ index) (upper : index < 1342976) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 1342720 then
    if cut : index < 1342592 then
      exact segment_sound _ 1342464 128 Restriction2622_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1342592 128 Restriction2622_1_checked index (by omega) (by omega)
  else
    if cut : index < 1342848 then
      exact segment_sound _ 1342720 128 Restriction2622_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 1342848 128 Restriction2622_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
