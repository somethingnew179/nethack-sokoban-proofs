import NetHack.Soko12Forward220.Unified.Reader
import NetHack.Soko12Forward220.Unified.Segment
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace NetHack.Soko12Forward220.Unified.Ground
open NetHack.Sokoban
theorem Restriction0282_0_checked : (List.range' 144384 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0282_1_checked : (List.range' 144512 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0282_2_checked : (List.range' 144640 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0282_3_checked : (List.range' 144768 128).all (fun index => PackedRestrictionChecks.check read cells packedRestrictions index) = true := by decide +kernel
theorem Restriction0282_range (index : Nat) (lower : 144384 ≤ index) (upper : index < 144896) : DecisionDAGTransform.restrictionCheck read restrictions index = true := by
  apply restriction_original_check
  if cut : index < 144640 then
    if cut : index < 144512 then
      exact segment_sound _ 144384 128 Restriction0282_0_checked index (by omega) (by omega)
    else
      exact segment_sound _ 144512 128 Restriction0282_1_checked index (by omega) (by omega)
  else
    if cut : index < 144768 then
      exact segment_sound _ 144640 128 Restriction0282_2_checked index (by omega) (by omega)
    else
      exact segment_sound _ 144768 128 Restriction0282_3_checked index (by omega) (by omega)
end NetHack.Soko12Forward220.Unified.Ground
