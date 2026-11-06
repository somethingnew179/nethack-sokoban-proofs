/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Substitutions21
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub2640 (p : Pattern) : d576 (change p 158 (some 159)) = d1442 p := by
  change (if p 139 then d2 (change p 158 (some 159)) else d540 (change p 158 (some 159))) = d1442 p
  rw [sub2587, sub2595]
  rfl
theorem sub2641 (p : Pattern) : d577 (change p 158 (some 159)) = d1443 p := by
  change (if p 138 then d576 (change p 158 (some 159)) else d540 (change p 158 (some 159))) = d1443 p
  rw [sub2640, sub2595]
  rfl
theorem sub2642 (p : Pattern) : d578 (change p 158 (some 159)) = d1444 p := by
  change (if p 139 then d2 (change p 158 (some 159)) else d546 (change p 158 (some 159))) = d1444 p
  rw [sub2587, sub2607]
  rfl
theorem sub2643 (p : Pattern) : d579 (change p 158 (some 159)) = d1445 p := by
  change (if p 138 then d578 (change p 158 (some 159)) else d546 (change p 158 (some 159))) = d1445 p
  rw [sub2642, sub2607]
  rfl
theorem sub2644 (p : Pattern) : d580 (change p 158 (some 159)) = d1446 p := by
  change (if p 134 then d579 (change p 158 (some 159)) else d577 (change p 158 (some 159))) = d1446 p
  rw [sub2643, sub2641]
  rfl
theorem sub2645 (p : Pattern) : d581 (change p 158 (some 159)) = d1447 p := by
  change (if p 133 then d580 (change p 158 (some 159)) else d575 (change p 158 (some 159))) = d1447 p
  rw [sub2644, sub2639]
  rfl
theorem sub2646 (p : Pattern) : d582 (change p 158 (some 159)) = d1448 p := by
  change (if p 132 then d581 (change p 158 (some 159)) else d550 (change p 158 (some 159))) = d1448 p
  rw [sub2645, sub2611]
  rfl
theorem sub2647 (p : Pattern) : d583 (change p 158 (some 159)) = d5 p := by
  change (if p 139 then d539 (change p 158 (some 159)) else d538 (change p 158 (some 159))) = d5 p
  rw [sub2591, sub2590]
  simp only [ite_self]
theorem sub2648 (p : Pattern) : d584 (change p 158 (some 159)) = d1414 p := by
  change (if p 138 then d541 (change p 158 (some 159)) else d583 (change p 158 (some 159))) = d1414 p
  rw [sub2596, sub2647]
  rfl
theorem sub2649 (p : Pattern) : d585 (change p 158 (some 159)) = d1417 p := by
  change (if p 134 then d548 (change p 158 (some 159)) else d584 (change p 158 (some 159))) = d1417 p
  rw [sub2609, sub2648]
  rfl
theorem sub2650 (p : Pattern) : d586 (change p 158 (some 159)) = d1449 p := by
  change (if p 134 then d578 (change p 158 (some 159)) else d576 (change p 158 (some 159))) = d1449 p
  rw [sub2642, sub2640]
  rfl
theorem sub2651 (p : Pattern) : d587 (change p 158 (some 159)) = d1450 p := by
  change (if p 133 then d586 (change p 158 (some 159)) else d585 (change p 158 (some 159))) = d1450 p
  rw [sub2650, sub2649]
  rfl
theorem sub2652 (p : Pattern) : d588 (change p 158 (some 159)) = d1451 p := by
  change (if p 132 then d587 (change p 158 (some 159)) else d550 (change p 158 (some 159))) = d1451 p
  rw [sub2651, sub2611]
  rfl
theorem sub2653 (p : Pattern) : d589 (change p 158 (some 159)) = d1452 p := by
  change (if p 113 then d588 (change p 158 (some 159)) else d582 (change p 158 (some 159))) = d1452 p
  rw [sub2652, sub2646]
  rfl
theorem sub2654 (p : Pattern) : d590 (change p 158 (some 159)) = d1453 p := by
  change (if p 133 then d586 (change p 158 (some 159)) else d557 (change p 158 (some 159))) = d1453 p
  rw [sub2650, sub2621]
  rfl
theorem sub2655 (p : Pattern) : d591 (change p 158 (some 159)) = d1454 p := by
  change (if p 132 then d590 (change p 158 (some 159)) else d558 (change p 158 (some 159))) = d1454 p
  rw [sub2654, sub2622]
  rfl
theorem sub2656 (p : Pattern) : d592 (change p 158 (some 159)) = d1455 p := by
  change (if p 133 then d586 (change p 158 (some 159)) else d566 (change p 158 (some 159))) = d1455 p
  rw [sub2650, sub2630]
  rfl
theorem sub2657 (p : Pattern) : d593 (change p 158 (some 159)) = d1456 p := by
  change (if p 132 then d592 (change p 158 (some 159)) else d567 (change p 158 (some 159))) = d1456 p
  rw [sub2656, sub2631]
  rfl
theorem sub2658 (p : Pattern) : d594 (change p 158 (some 159)) = d1457 p := by
  change (if p 113 then d593 (change p 158 (some 159)) else d591 (change p 158 (some 159))) = d1457 p
  rw [sub2657, sub2655]
  rfl
theorem sub2659 (p : Pattern) : d595 (change p 158 (some 159)) = d1458 p := by
  change (if p 112 then d594 (change p 158 (some 159)) else d589 (change p 158 (some 159))) = d1458 p
  rw [sub2658, sub2653]
  rfl
theorem sub2660 (p : Pattern) : d596 (change p 158 (some 159)) = d1459 p := by
  change (if p 106 then d595 (change p 158 (some 159)) else d574 (change p 158 (some 159))) = d1459 p
  rw [sub2659, sub2638]
  rfl
theorem sub2661 (p : Pattern) : d597 (change p 158 (some 159)) = d1460 p := by
  change (if p 138 then d562 (change p 158 (some 159)) else d538 (change p 158 (some 159))) = d1460 p
  rw [sub2626, sub2590]
  rfl
theorem sub2662 (p : Pattern) : d598 (change p 158 (some 159)) = d1460 p := by
  change (if p 138 then d562 (change p 158 (some 159)) else d539 (change p 158 (some 159))) = d1460 p
  rw [sub2626, sub2591]
  rfl
theorem sub2663 (p : Pattern) : d599 (change p 158 (some 159)) = d1460 p := by
  change (if p 134 then d598 (change p 158 (some 159)) else d597 (change p 158 (some 159))) = d1460 p
  rw [sub2662, sub2661]
  simp only [ite_self]
theorem sub2664 (p : Pattern) : d600 (change p 158 (some 159)) = d1461 p := by
  change (if p 138 then d564 (change p 158 (some 159)) else d545 (change p 158 (some 159))) = d1461 p
  rw [sub2628, sub2603]
  rfl
theorem sub2665 (p : Pattern) : d601 (change p 158 (some 159)) = d1462 p := by
  change (if p 134 then d600 (change p 158 (some 159)) else d598 (change p 158 (some 159))) = d1462 p
  rw [sub2664, sub2662]
  rfl
theorem sub2666 (p : Pattern) : d602 (change p 158 (some 159)) = d1463 p := by
  change (if p 133 then d601 (change p 158 (some 159)) else d599 (change p 158 (some 159))) = d1463 p
  rw [sub2665, sub2663]
  rfl
theorem sub2667 (p : Pattern) : d603 (change p 158 (some 159)) = d1460 p := by
  change (if p 138 then d562 (change p 158 (some 159)) else d583 (change p 158 (some 159))) = d1460 p
  rw [sub2626, sub2647]
  rfl
theorem sub2668 (p : Pattern) : d604 (change p 158 (some 159)) = d1464 p := by
  change (if p 138 then d568 (change p 158 (some 159)) else d551 (change p 158 (some 159))) = d1464 p
  rw [sub2632, sub2615]
  rfl
theorem sub2669 (p : Pattern) : d605 (change p 158 (some 159)) = d1465 p := by
  change (if p 134 then d604 (change p 158 (some 159)) else d603 (change p 158 (some 159))) = d1465 p
  rw [sub2668, sub2667]
  rfl
theorem sub2670 (p : Pattern) : d606 (change p 158 (some 159)) = d1466 p := by
  change (if p 133 then d601 (change p 158 (some 159)) else d605 (change p 158 (some 159))) = d1466 p
  rw [sub2665, sub2669]
  rfl
theorem sub2671 (p : Pattern) : d607 (change p 158 (some 159)) = d1467 p := by
  change (if p 132 then d606 (change p 158 (some 159)) else d602 (change p 158 (some 159))) = d1467 p
  rw [sub2670, sub2666]
  rfl
theorem sub2672 (p : Pattern) : d608 (change p 158 (some 159)) = d1468 p := by
  change (if p 113 then d607 (change p 158 (some 159)) else d556 (change p 158 (some 159))) = d1468 p
  rw [sub2671, sub2620]
  rfl
theorem sub2673 (p : Pattern) : d609 (change p 158 (some 159)) = d1469 p := by
  change (if p 133 then d580 (change p 158 (some 159)) else d577 (change p 158 (some 159))) = d1469 p
  rw [sub2644, sub2641]
  rfl
theorem sub2674 (p : Pattern) : d610 (change p 158 (some 159)) = d1470 p := by
  change (if p 132 then d580 (change p 158 (some 159)) else d609 (change p 158 (some 159))) = d1470 p
  rw [sub2644, sub2673]
  rfl
theorem sub2675 (p : Pattern) : d611 (change p 158 (some 159)) = d1471 p := by
  change (if p 112 then d610 (change p 158 (some 159)) else d608 (change p 158 (some 159))) = d1471 p
  rw [sub2674, sub2672]
  rfl
theorem sub2676 (p : Pattern) : d612 (change p 158 (some 159)) = d1460 p := by
  change (if p 134 then d598 (change p 158 (some 159)) else d603 (change p 158 (some 159))) = d1460 p
  rw [sub2662, sub2667]
  simp only [ite_self]
theorem sub2677 (p : Pattern) : d613 (change p 158 (some 159)) = d1463 p := by
  change (if p 133 then d601 (change p 158 (some 159)) else d612 (change p 158 (some 159))) = d1463 p
  rw [sub2665, sub2676]
  rfl
theorem sub2678 (p : Pattern) : d614 (change p 158 (some 159)) = d1472 p := by
  change (if p 133 then d586 (change p 158 (some 159)) else d601 (change p 158 (some 159))) = d1472 p
  rw [sub2650, sub2665]
  rfl
theorem sub2679 (p : Pattern) : d615 (change p 158 (some 159)) = d1473 p := by
  change (if p 132 then d614 (change p 158 (some 159)) else d613 (change p 158 (some 159))) = d1473 p
  rw [sub2678, sub2677]
  rfl
theorem sub2680 (p : Pattern) : d616 (change p 158 (some 159)) = d1474 p := by
  change (if p 113 then d615 (change p 158 (some 159)) else d588 (change p 158 (some 159))) = d1474 p
  rw [sub2679, sub2652]
  rfl
theorem sub2681 (p : Pattern) : d617 (change p 158 (some 159)) = d1475 p := by
  change (if p 133 then d2 (change p 158 (some 159)) else d580 (change p 158 (some 159))) = d1475 p
  rw [sub2587, sub2644]
  rfl
theorem sub2682 (p : Pattern) : d618 (change p 158 (some 159)) = d1476 p := by
  change (if p 132 then d617 (change p 158 (some 159)) else d609 (change p 158 (some 159))) = d1476 p
  rw [sub2681, sub2673]
  rfl
theorem sub2683 (p : Pattern) : d619 (change p 158 (some 159)) = d1477 p := by
  change (if p 133 then d586 (change p 158 (some 159)) else d576 (change p 158 (some 159))) = d1477 p
  rw [sub2650, sub2640]
  rfl
theorem sub2684 (p : Pattern) : d620 (change p 158 (some 159)) = d1478 p := by
  change (if p 133 then d2 (change p 158 (some 159)) else d586 (change p 158 (some 159))) = d1478 p
  rw [sub2587, sub2650]
  rfl
theorem sub2685 (p : Pattern) : d621 (change p 158 (some 159)) = d1479 p := by
  change (if p 132 then d620 (change p 158 (some 159)) else d619 (change p 158 (some 159))) = d1479 p
  rw [sub2684, sub2683]
  rfl
theorem sub2686 (p : Pattern) : d622 (change p 158 (some 159)) = d1480 p := by
  change (if p 113 then d621 (change p 158 (some 159)) else d618 (change p 158 (some 159))) = d1480 p
  rw [sub2685, sub2682]
  rfl
theorem sub2687 (p : Pattern) : d623 (change p 158 (some 159)) = d1481 p := by
  change (if p 112 then d622 (change p 158 (some 159)) else d616 (change p 158 (some 159))) = d1481 p
  rw [sub2686, sub2680]
  rfl
theorem sub2688 (p : Pattern) : d624 (change p 158 (some 159)) = d1482 p := by
  change (if p 106 then d623 (change p 158 (some 159)) else d611 (change p 158 (some 159))) = d1482 p
  rw [sub2687, sub2675]
  rfl
theorem sub2689 (p : Pattern) : d625 (change p 158 (some 159)) = d1483 p := by
  change (if p 86 then d624 (change p 158 (some 159)) else d596 (change p 158 (some 159))) = d1483 p
  rw [sub2688, sub2660]
  rfl
theorem sub2690 (p : Pattern) : d626 (change p 158 (some 159)) = d1421 p := by
  change (if p 134 then d553 (change p 158 (some 159)) else d584 (change p 158 (some 159))) = d1421 p
  rw [sub2617, sub2648]
  rfl
theorem sub2691 (p : Pattern) : d627 (change p 158 (some 159)) = d1422 p := by
  change (if p 133 then d549 (change p 158 (some 159)) else d626 (change p 158 (some 159))) = d1422 p
  rw [sub2610, sub2690]
  rfl
theorem sub2692 (p : Pattern) : d628 (change p 158 (some 159)) = d1423 p := by
  change (if p 132 then d627 (change p 158 (some 159)) else d550 (change p 158 (some 159))) = d1423 p
  rw [sub2691, sub2611]
  rfl
theorem sub2693 (p : Pattern) : d629 (change p 158 (some 159)) = d1423 p := by
  change (if p 113 then d628 (change p 158 (some 159)) else d556 (change p 158 (some 159))) = d1423 p
  rw [sub2692, sub2620]
  simp only [ite_self]
theorem sub2694 (p : Pattern) : d630 (change p 158 (some 159)) = d1441 p := by
  change (if p 112 then d573 (change p 158 (some 159)) else d629 (change p 158 (some 159))) = d1441 p
  rw [sub2637, sub2693]
  rfl
theorem sub2695 (p : Pattern) : d631 (change p 158 (some 159)) = d1414 p := by
  change (if p 134 then d543 (change p 158 (some 159)) else d584 (change p 158 (some 159))) = d1414 p
  rw [sub2598, sub2648]
  simp only [ite_self]
theorem sub2696 (p : Pattern) : d632 (change p 158 (some 159)) = d1418 p := by
  change (if p 133 then d549 (change p 158 (some 159)) else d631 (change p 158 (some 159))) = d1418 p
  rw [sub2610, sub2695]
  rfl
theorem sub2697 (p : Pattern) : d633 (change p 158 (some 159)) = d1450 p := by
  change (if p 133 then d586 (change p 158 (some 159)) else d549 (change p 158 (some 159))) = d1450 p
  rw [sub2650, sub2610]
  rfl
theorem sub2698 (p : Pattern) : d634 (change p 158 (some 159)) = d1451 p := by
  change (if p 132 then d633 (change p 158 (some 159)) else d632 (change p 158 (some 159))) = d1451 p
  rw [sub2697, sub2696]
  rfl
theorem sub2699 (p : Pattern) : d635 (change p 158 (some 159)) = d1451 p := by
  change (if p 113 then d634 (change p 158 (some 159)) else d588 (change p 158 (some 159))) = d1451 p
  rw [sub2698, sub2652]
  simp only [ite_self]
theorem sub2700 (p : Pattern) : d636 (change p 158 (some 159)) = d1484 p := by
  change (if p 112 then d594 (change p 158 (some 159)) else d635 (change p 158 (some 159))) = d1484 p
  rw [sub2658, sub2699]
  rfl
theorem sub2701 (p : Pattern) : d637 (change p 158 (some 159)) = d1485 p := by
  change (if p 106 then d636 (change p 158 (some 159)) else d630 (change p 158 (some 159))) = d1485 p
  rw [sub2700, sub2694]
  rfl
theorem sub2702 (p : Pattern) : d638 (change p 158 (some 159)) = d1486 p := by
  change (if p 139 then d545 (change p 158 (some 159)) else d551 (change p 158 (some 159))) = d1486 p
  rw [sub2603, sub2615]
  rfl
theorem sub2703 (p : Pattern) : d639 (change p 158 (some 159)) = d1487 p := by
  change (if p 138 then d568 (change p 158 (some 159)) else d638 (change p 158 (some 159))) = d1487 p
  rw [sub2632, sub2702]
  rfl
theorem sub2704 (p : Pattern) : d640 (change p 158 (some 159)) = d1488 p := by
  change (if p 134 then d639 (change p 158 (some 159)) else d598 (change p 158 (some 159))) = d1488 p
  rw [sub2703, sub2662]
  rfl
theorem sub2705 (p : Pattern) : d641 (change p 158 (some 159)) = d1489 p := by
  change (if p 133 then d601 (change p 158 (some 159)) else d640 (change p 158 (some 159))) = d1489 p
  rw [sub2665, sub2704]
  rfl
theorem sub2706 (p : Pattern) : d642 (change p 158 (some 159)) = d1490 p := by
  change (if p 132 then d641 (change p 158 (some 159)) else d613 (change p 158 (some 159))) = d1490 p
  rw [sub2705, sub2677]
  rfl
theorem sub2707 (p : Pattern) : d643 (change p 158 (some 159)) = d1491 p := by
  change (if p 113 then d642 (change p 158 (some 159)) else d628 (change p 158 (some 159))) = d1491 p
  rw [sub2706, sub2692]
  rfl
theorem sub2708 (p : Pattern) : d644 (change p 158 (some 159)) = d1492 p := by
  change (if p 132 then d586 (change p 158 (some 159)) else d619 (change p 158 (some 159))) = d1492 p
  rw [sub2650, sub2683]
  rfl
theorem sub2709 (p : Pattern) : d645 (change p 158 (some 159)) = d1493 p := by
  change (if p 113 then d644 (change p 158 (some 159)) else d610 (change p 158 (some 159))) = d1493 p
  rw [sub2708, sub2674]
  rfl
theorem sub2710 (p : Pattern) : d646 (change p 158 (some 159)) = d1494 p := by
  change (if p 112 then d645 (change p 158 (some 159)) else d643 (change p 158 (some 159))) = d1494 p
  rw [sub2709, sub2707]
  rfl
theorem sub2711 (p : Pattern) : d647 (change p 158 (some 159)) = d1495 p := by
  change (if p 113 then d593 (change p 158 (some 159)) else d634 (change p 158 (some 159))) = d1495 p
  rw [sub2657, sub2698]
  rfl
theorem sub2712 (p : Pattern) : d648 (change p 158 (some 159)) = d1496 p := by
  change (if p 113 then d2 (change p 158 (some 159)) else d621 (change p 158 (some 159))) = d1496 p
  rw [sub2587, sub2685]
  rfl
theorem sub2713 (p : Pattern) : d649 (change p 158 (some 159)) = d1497 p := by
  change (if p 112 then d648 (change p 158 (some 159)) else d647 (change p 158 (some 159))) = d1497 p
  rw [sub2712, sub2711]
  rfl
theorem sub2714 (p : Pattern) : d650 (change p 158 (some 159)) = d1498 p := by
  change (if p 106 then d649 (change p 158 (some 159)) else d646 (change p 158 (some 159))) = d1498 p
  rw [sub2713, sub2710]
  rfl
theorem sub2715 (p : Pattern) : d651 (change p 158 (some 159)) = d1499 p := by
  change (if p 86 then d650 (change p 158 (some 159)) else d637 (change p 158 (some 159))) = d1499 p
  rw [sub2714, sub2701]
  rfl
theorem sub2716 (p : Pattern) : d652 (change p 158 (some 159)) = d1500 p := by
  change (if p 80 then d651 (change p 158 (some 159)) else d625 (change p 158 (some 159))) = d1500 p
  rw [sub2715, sub2689]
  rfl
theorem sub2717 (p : Pattern) : d0 (change p 132 (some 106)) = d0 p := by
  rfl
theorem sub2718 (p : Pattern) : d2 (change p 132 (some 106)) = d2 p := by
  rfl
theorem sub2719 (p : Pattern) : d3 (change p 132 (some 106)) = d3 p := by
  change (if p 161 then d2 (change p 132 (some 106)) else d0 (change p 132 (some 106))) = d3 p
  rw [sub2718, sub2717]
  rfl
theorem sub2720 (p : Pattern) : d4 (change p 132 (some 106)) = d4 p := by
  change (if p 160 then d3 (change p 132 (some 106)) else d0 (change p 132 (some 106))) = d4 p
  rw [sub2719, sub2717]
  rfl
theorem sub2721 (p : Pattern) : d5 (change p 132 (some 106)) = d5 p := by
  change (if p 160 then d2 (change p 132 (some 106)) else d0 (change p 132 (some 106))) = d5 p
  rw [sub2718, sub2717]
  rfl
theorem sub2722 (p : Pattern) : d6 (change p 132 (some 106)) = d6 p := by
  change (if p 159 then d5 (change p 132 (some 106)) else d4 (change p 132 (some 106))) = d6 p
  rw [sub2721, sub2720]
  rfl
theorem sub2723 (p : Pattern) : d7 (change p 132 (some 106)) = d7 p := by
  change (if p 159 then d2 (change p 132 (some 106)) else d4 (change p 132 (some 106))) = d7 p
  rw [sub2718, sub2720]
  rfl
theorem sub2724 (p : Pattern) : d8 (change p 132 (some 106)) = d8 p := by
  change (if p 158 then d7 (change p 132 (some 106)) else d6 (change p 132 (some 106))) = d8 p
  rw [sub2723, sub2722]
  rfl
theorem sub2725 (p : Pattern) : d1 (change p 132 (some 106)) = d1 p := by
  rfl
theorem sub2726 (p : Pattern) : d9 (change p 132 (some 106)) = d9 p := by
  change (if p 161 then d2 (change p 132 (some 106)) else d1 (change p 132 (some 106))) = d9 p
  rw [sub2718, sub2725]
  rfl
theorem sub2727 (p : Pattern) : d10 (change p 132 (some 106)) = d10 p := by
  change (if p 160 then d9 (change p 132 (some 106)) else d1 (change p 132 (some 106))) = d10 p
  rw [sub2726, sub2725]
  rfl
theorem sub2728 (p : Pattern) : d11 (change p 132 (some 106)) = d11 p := by
  change (if p 160 then d2 (change p 132 (some 106)) else d1 (change p 132 (some 106))) = d11 p
  rw [sub2718, sub2725]
  rfl
theorem sub2729 (p : Pattern) : d12 (change p 132 (some 106)) = d12 p := by
  change (if p 159 then d11 (change p 132 (some 106)) else d10 (change p 132 (some 106))) = d12 p
  rw [sub2728, sub2727]
  rfl
theorem sub2730 (p : Pattern) : d13 (change p 132 (some 106)) = d13 p := by
  change (if p 159 then d2 (change p 132 (some 106)) else d10 (change p 132 (some 106))) = d13 p
  rw [sub2718, sub2727]
  rfl
theorem sub2731 (p : Pattern) : d14 (change p 132 (some 106)) = d14 p := by
  change (if p 158 then d13 (change p 132 (some 106)) else d12 (change p 132 (some 106))) = d14 p
  rw [sub2730, sub2729]
  rfl
theorem sub2732 (p : Pattern) : d15 (change p 132 (some 106)) = d15 p := by
  change (if p 139 then d14 (change p 132 (some 106)) else d8 (change p 132 (some 106))) = d15 p
  rw [sub2731, sub2724]
  rfl
theorem sub2733 (p : Pattern) : d16 (change p 132 (some 106)) = d16 p := by
  change (if p 138 then d15 (change p 132 (some 106)) else d8 (change p 132 (some 106))) = d16 p
  rw [sub2732, sub2724]
  rfl
theorem sub2734 (p : Pattern) : d17 (change p 132 (some 106)) = d17 p := by
  change (if p 160 then d2 (change p 132 (some 106)) else d3 (change p 132 (some 106))) = d17 p
  rw [sub2718, sub2719]
  rfl
theorem sub2735 (p : Pattern) : d18 (change p 132 (some 106)) = d18 p := by
  change (if p 159 then d17 (change p 132 (some 106)) else d4 (change p 132 (some 106))) = d18 p
  rw [sub2734, sub2720]
  rfl
theorem sub2736 (p : Pattern) : d19 (change p 132 (some 106)) = d19 p := by
  change (if p 159 then d2 (change p 132 (some 106)) else d17 (change p 132 (some 106))) = d19 p
  rw [sub2718, sub2734]
  rfl
theorem sub2737 (p : Pattern) : d20 (change p 132 (some 106)) = d20 p := by
  change (if p 158 then d19 (change p 132 (some 106)) else d18 (change p 132 (some 106))) = d20 p
  rw [sub2736, sub2735]
  rfl
theorem sub2738 (p : Pattern) : d21 (change p 132 (some 106)) = d21 p := by
  change (if p 160 then d2 (change p 132 (some 106)) else d9 (change p 132 (some 106))) = d21 p
  rw [sub2718, sub2726]
  rfl
theorem sub2739 (p : Pattern) : d22 (change p 132 (some 106)) = d22 p := by
  change (if p 159 then d21 (change p 132 (some 106)) else d10 (change p 132 (some 106))) = d22 p
  rw [sub2738, sub2727]
  rfl
theorem sub2740 (p : Pattern) : d23 (change p 132 (some 106)) = d23 p := by
  change (if p 159 then d2 (change p 132 (some 106)) else d21 (change p 132 (some 106))) = d23 p
  rw [sub2718, sub2738]
  rfl
theorem sub2741 (p : Pattern) : d24 (change p 132 (some 106)) = d24 p := by
  change (if p 158 then d23 (change p 132 (some 106)) else d22 (change p 132 (some 106))) = d24 p
  rw [sub2740, sub2739]
  rfl
theorem sub2742 (p : Pattern) : d25 (change p 132 (some 106)) = d25 p := by
  change (if p 139 then d24 (change p 132 (some 106)) else d20 (change p 132 (some 106))) = d25 p
  rw [sub2741, sub2737]
  rfl
theorem sub2743 (p : Pattern) : d26 (change p 132 (some 106)) = d26 p := by
  change (if p 138 then d25 (change p 132 (some 106)) else d20 (change p 132 (some 106))) = d26 p
  rw [sub2742, sub2737]
  rfl
theorem sub2744 (p : Pattern) : d27 (change p 132 (some 106)) = d27 p := by
  change (if p 134 then d26 (change p 132 (some 106)) else d16 (change p 132 (some 106))) = d27 p
  rw [sub2743, sub2733]
  rfl
theorem sub2745 (p : Pattern) : d28 (change p 132 (some 106)) = d28 p := by
  change (if p 133 then d27 (change p 132 (some 106)) else d16 (change p 132 (some 106))) = d28 p
  rw [sub2744, sub2733]
  rfl
theorem sub2746 (p : Pattern) : d256 (change p 132 (some 106)) = d28 p := by
  change d28 (change p 132 (some 106)) = d28 p
  exact sub2745 p
theorem sub2747 (p : Pattern) : d261 (change p 132 (some 106)) = d28 p := by
  change d28 (change p 132 (some 106)) = d28 p
  exact sub2745 p
theorem sub2748 (p : Pattern) : d262 (change p 132 (some 106)) = d28 p := by
  change (if p 113 then d261 (change p 132 (some 106)) else d256 (change p 132 (some 106))) = d28 p
  rw [sub2747, sub2746]
  simp only [ite_self]
theorem sub2749 (p : Pattern) : d46 (change p 132 (some 106)) = d46 p := by
  change (if p 134 then d25 (change p 132 (some 106)) else d15 (change p 132 (some 106))) = d46 p
  rw [sub2742, sub2732]
  rfl
theorem sub2750 (p : Pattern) : d47 (change p 132 (some 106)) = d47 p := by
  change (if p 133 then d46 (change p 132 (some 106)) else d15 (change p 132 (some 106))) = d47 p
  rw [sub2749, sub2732]
  rfl
theorem sub2751 (p : Pattern) : d257 (change p 132 (some 106)) = d47 p := by
  change d47 (change p 132 (some 106)) = d47 p
  exact sub2750 p
theorem sub2752 (p : Pattern) : d52 (change p 132 (some 106)) = d52 p := by
  change (if p 139 then d2 (change p 132 (some 106)) else d8 (change p 132 (some 106))) = d52 p
  rw [sub2718, sub2724]
  rfl
theorem sub2753 (p : Pattern) : d53 (change p 132 (some 106)) = d53 p := by
  change (if p 138 then d52 (change p 132 (some 106)) else d15 (change p 132 (some 106))) = d53 p
  rw [sub2752, sub2732]
  rfl
theorem sub2754 (p : Pattern) : d54 (change p 132 (some 106)) = d54 p := by
  change (if p 139 then d2 (change p 132 (some 106)) else d20 (change p 132 (some 106))) = d54 p
  rw [sub2718, sub2737]
  rfl
theorem sub2755 (p : Pattern) : d55 (change p 132 (some 106)) = d55 p := by
  change (if p 138 then d54 (change p 132 (some 106)) else d25 (change p 132 (some 106))) = d55 p
  rw [sub2754, sub2742]
  rfl
theorem sub2756 (p : Pattern) : d56 (change p 132 (some 106)) = d56 p := by
  change (if p 134 then d55 (change p 132 (some 106)) else d53 (change p 132 (some 106))) = d56 p
  rw [sub2755, sub2753]
  rfl
theorem sub2757 (p : Pattern) : d57 (change p 132 (some 106)) = d57 p := by
  change (if p 133 then d56 (change p 132 (some 106)) else d53 (change p 132 (some 106))) = d57 p
  rw [sub2756, sub2753]
  rfl
theorem sub2758 (p : Pattern) : d263 (change p 132 (some 106)) = d57 p := by
  change d57 (change p 132 (some 106)) = d57 p
  exact sub2757 p
theorem sub2759 (p : Pattern) : d264 (change p 132 (some 106)) = d1223 p := by
  change (if p 113 then d263 (change p 132 (some 106)) else d257 (change p 132 (some 106))) = d1223 p
  rw [sub2758, sub2751]
  rfl
end NetHack.Sokoban32Refined
