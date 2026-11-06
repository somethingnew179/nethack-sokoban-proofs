/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Substitutions79
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem sub9600 (p : Pattern) : d17 (change p 225 none) = d17 p := by
  change (if p 247 then d12 (change p 225 none) else d4 (change p 225 none)) = d17 p
  rw [sub9592, sub9598]
  rfl
theorem sub9601 (p : Pattern) : d1770 (change p 225 none) = d1770 p := by
  change (if p 246 then d17 (change p 225 none) else d1769 (change p 225 none)) = d1770 p
  rw [sub9600, sub9599]
  rfl
theorem sub9602 (p : Pattern) : d2506 (change p 225 none) = d1770 p := by
  change d1770 (change p 225 none) = d1770 p
  exact sub9601 p
theorem sub9603 (p : Pattern) : d2507 (change p 225 none) = d5541 p := by
  change (if p 224 then d2506 (change p 225 none) else d2504 (change p 225 none)) = d5541 p
  rw [sub9602, sub9596]
  rfl
theorem sub9604 (p : Pattern) : d2508 (change p 225 none) = d5542 p := by
  change (if p 204 then d2507 (change p 225 none) else d2505 (change p 225 none)) = d5542 p
  rw [sub9603, sub9597]
  rfl
theorem sub9605 (p : Pattern) : d2 (change p 225 none) = d2 p := by
  rfl
theorem sub9606 (p : Pattern) : d1683 (change p 225 none) = d1683 p := by
  change (if p 247 then d2 (change p 225 none) else d0 (change p 225 none)) = d1683 p
  rw [sub9605, sub9591]
  rfl
theorem sub9607 (p : Pattern) : d30 (change p 225 none) = d30 p := by
  change (if p 247 then d12 (change p 225 none) else d2 (change p 225 none)) = d30 p
  rw [sub9592, sub9605]
  rfl
theorem sub9608 (p : Pattern) : d1684 (change p 225 none) = d1684 p := by
  change (if p 246 then d30 (change p 225 none) else d1683 (change p 225 none)) = d1684 p
  rw [sub9607, sub9606]
  rfl
theorem sub9609 (p : Pattern) : d2509 (change p 225 none) = d1684 p := by
  change d1684 (change p 225 none) = d1684 p
  exact sub9608 p
theorem sub9610 (p : Pattern) : d2510 (change p 225 none) = d5543 p := by
  change (if p 224 then d2509 (change p 225 none) else d2504 (change p 225 none)) = d5543 p
  rw [sub9609, sub9596]
  rfl
theorem sub9611 (p : Pattern) : d2511 (change p 225 none) = d5544 p := by
  change (if p 204 then d12 (change p 225 none) else d2510 (change p 225 none)) = d5544 p
  rw [sub9592, sub9610]
  rfl
theorem sub9612 (p : Pattern) : d2512 (change p 225 none) = d5545 p := by
  change (if p 182 then d2511 (change p 225 none) else d2508 (change p 225 none)) = d5545 p
  rw [sub9611, sub9604]
  rfl
theorem sub9613 (p : Pattern) : d2513 (change p 225 none) = d14 p := by
  change d14 (change p 225 none) = d14 p
  exact sub9594 p
theorem sub9614 (p : Pattern) : d2514 (change p 225 none) = d14 p := by
  change (if p 224 then d2504 (change p 225 none) else d2513 (change p 225 none)) = d14 p
  rw [sub9596, sub9613]
  simp only [ite_self]
theorem sub9615 (p : Pattern) : d2515 (change p 225 none) = d5542 p := by
  change (if p 204 then d2507 (change p 225 none) else d2514 (change p 225 none)) = d5542 p
  rw [sub9603, sub9614]
  rfl
theorem sub9616 (p : Pattern) : d2516 (change p 225 none) = d5545 p := by
  change (if p 182 then d2511 (change p 225 none) else d2515 (change p 225 none)) = d5545 p
  rw [sub9611, sub9615]
  rfl
theorem sub9617 (p : Pattern) : d2517 (change p 225 none) = d5545 p := by
  change (if p 163 then d2516 (change p 225 none) else d2512 (change p 225 none)) = d5545 p
  rw [sub9616, sub9612]
  simp only [ite_self]
theorem sub9618 (p : Pattern) : d2518 (change p 225 none) = d5542 p := by
  change (if p 204 then d2507 (change p 225 none) else d2504 (change p 225 none)) = d5542 p
  rw [sub9603, sub9596]
  rfl
theorem sub9619 (p : Pattern) : d2519 (change p 225 none) = d5545 p := by
  change (if p 182 then d2511 (change p 225 none) else d2518 (change p 225 none)) = d5545 p
  rw [sub9611, sub9618]
  rfl
theorem sub9620 (p : Pattern) : d18 (change p 225 none) = d18 p := by
  change (if p 246 then d17 (change p 225 none) else d4 (change p 225 none)) = d18 p
  rw [sub9600, sub9598]
  rfl
theorem sub9621 (p : Pattern) : d2520 (change p 225 none) = d18 p := by
  change d18 (change p 225 none) = d18 p
  exact sub9620 p
theorem sub9622 (p : Pattern) : d8 (change p 225 none) = d8 p := by
  rfl
theorem sub9623 (p : Pattern) : d1794 (change p 225 none) = d1794 p := by
  change (if p 247 then d8 (change p 225 none) else d4 (change p 225 none)) = d1794 p
  rw [sub9622, sub9598]
  rfl
theorem sub9624 (p : Pattern) : d190 (change p 225 none) = d190 p := by
  change (if p 247 then d12 (change p 225 none) else d8 (change p 225 none)) = d190 p
  rw [sub9592, sub9622]
  rfl
theorem sub9625 (p : Pattern) : d1795 (change p 225 none) = d1795 p := by
  change (if p 246 then d190 (change p 225 none) else d1794 (change p 225 none)) = d1795 p
  rw [sub9624, sub9623]
  rfl
theorem sub9626 (p : Pattern) : d2521 (change p 225 none) = d1795 p := by
  change d1795 (change p 225 none) = d1795 p
  exact sub9625 p
theorem sub9627 (p : Pattern) : d2522 (change p 225 none) = d5546 p := by
  change (if p 224 then d2521 (change p 225 none) else d2520 (change p 225 none)) = d5546 p
  rw [sub9626, sub9621]
  rfl
theorem sub9628 (p : Pattern) : d2523 (change p 225 none) = d5547 p := by
  change (if p 204 then d2522 (change p 225 none) else d2520 (change p 225 none)) = d5547 p
  rw [sub9627, sub9621]
  rfl
theorem sub9629 (p : Pattern) : d6 (change p 225 none) = d6 p := by
  rfl
theorem sub9630 (p : Pattern) : d1693 (change p 225 none) = d1693 p := by
  change (if p 247 then d6 (change p 225 none) else d4 (change p 225 none)) = d1693 p
  rw [sub9629, sub9598]
  rfl
theorem sub9631 (p : Pattern) : d34 (change p 225 none) = d34 p := by
  change (if p 247 then d12 (change p 225 none) else d6 (change p 225 none)) = d34 p
  rw [sub9592, sub9629]
  rfl
theorem sub9632 (p : Pattern) : d1694 (change p 225 none) = d1694 p := by
  change (if p 246 then d34 (change p 225 none) else d1693 (change p 225 none)) = d1694 p
  rw [sub9631, sub9630]
  rfl
theorem sub9633 (p : Pattern) : d2524 (change p 225 none) = d1694 p := by
  change d1694 (change p 225 none) = d1694 p
  exact sub9632 p
theorem sub9634 (p : Pattern) : d2525 (change p 225 none) = d5548 p := by
  change (if p 224 then d2524 (change p 225 none) else d2520 (change p 225 none)) = d5548 p
  rw [sub9633, sub9621]
  rfl
theorem sub9635 (p : Pattern) : d2526 (change p 225 none) = d5549 p := by
  change (if p 204 then d12 (change p 225 none) else d2525 (change p 225 none)) = d5549 p
  rw [sub9592, sub9634]
  rfl
theorem sub9636 (p : Pattern) : d2527 (change p 225 none) = d5550 p := by
  change (if p 182 then d2526 (change p 225 none) else d2523 (change p 225 none)) = d5550 p
  rw [sub9635, sub9628]
  rfl
theorem sub9637 (p : Pattern) : d2528 (change p 225 none) = d5551 p := by
  change (if p 163 then d2527 (change p 225 none) else d2519 (change p 225 none)) = d5551 p
  rw [sub9636, sub9619]
  rfl
theorem sub9638 (p : Pattern) : d2529 (change p 225 none) = d5552 p := by
  change (if p 162 then d2528 (change p 225 none) else d2517 (change p 225 none)) = d5552 p
  rw [sub9637, sub9617]
  rfl
theorem sub9639 (p : Pattern) : d9 (change p 225 none) = d9 p := by
  rfl
theorem sub9640 (p : Pattern) : d23 (change p 225 none) = d23 p := by
  change (if p 247 then d12 (change p 225 none) else d9 (change p 225 none)) = d23 p
  rw [sub9592, sub9639]
  rfl
theorem sub9641 (p : Pattern) : d24 (change p 225 none) = d24 p := by
  change (if p 246 then d23 (change p 225 none) else d9 (change p 225 none)) = d24 p
  rw [sub9640, sub9639]
  rfl
theorem sub9642 (p : Pattern) : d2530 (change p 225 none) = d24 p := by
  change d24 (change p 225 none) = d24 p
  exact sub9641 p
theorem sub9643 (p : Pattern) : d356 (change p 225 none) = d356 p := by
  change (if p 246 then d12 (change p 225 none) else d23 (change p 225 none)) = d356 p
  rw [sub9592, sub9640]
  rfl
theorem sub9644 (p : Pattern) : d357 (change p 225 none) = d356 p := by
  change d356 (change p 225 none) = d356 p
  exact sub9643 p
theorem sub9645 (p : Pattern) : d2531 (change p 225 none) = d5553 p := by
  change (if p 224 then d357 (change p 225 none) else d2530 (change p 225 none)) = d5553 p
  rw [sub9644, sub9642]
  rfl
theorem sub9646 (p : Pattern) : d2532 (change p 225 none) = d5554 p := by
  change (if p 204 then d2531 (change p 225 none) else d2530 (change p 225 none)) = d5554 p
  rw [sub9645, sub9642]
  rfl
theorem sub9647 (p : Pattern) : d11 (change p 225 none) = d11 p := by
  rfl
theorem sub9648 (p : Pattern) : d1701 (change p 225 none) = d1701 p := by
  change (if p 247 then d11 (change p 225 none) else d9 (change p 225 none)) = d1701 p
  rw [sub9647, sub9639]
  rfl
theorem sub9649 (p : Pattern) : d39 (change p 225 none) = d39 p := by
  change (if p 247 then d12 (change p 225 none) else d11 (change p 225 none)) = d39 p
  rw [sub9592, sub9647]
  rfl
theorem sub9650 (p : Pattern) : d1702 (change p 225 none) = d1702 p := by
  change (if p 246 then d39 (change p 225 none) else d1701 (change p 225 none)) = d1702 p
  rw [sub9649, sub9648]
  rfl
theorem sub9651 (p : Pattern) : d2533 (change p 225 none) = d1702 p := by
  change d1702 (change p 225 none) = d1702 p
  exact sub9650 p
theorem sub9652 (p : Pattern) : d2534 (change p 225 none) = d5555 p := by
  change (if p 224 then d2533 (change p 225 none) else d2530 (change p 225 none)) = d5555 p
  rw [sub9651, sub9642]
  rfl
theorem sub9653 (p : Pattern) : d2535 (change p 225 none) = d5556 p := by
  change (if p 204 then d12 (change p 225 none) else d2534 (change p 225 none)) = d5556 p
  rw [sub9592, sub9652]
  rfl
theorem sub9654 (p : Pattern) : d2536 (change p 225 none) = d5557 p := by
  change (if p 182 then d2535 (change p 225 none) else d2532 (change p 225 none)) = d5557 p
  rw [sub9653, sub9646]
  rfl
theorem sub9655 (p : Pattern) : d2537 (change p 225 none) = d5558 p := by
  change (if p 163 then d12 (change p 225 none) else d2536 (change p 225 none)) = d5558 p
  rw [sub9592, sub9654]
  rfl
theorem sub9656 (p : Pattern) : d2538 (change p 225 none) = d5559 p := by
  change (if p 162 then d2537 (change p 225 none) else d2528 (change p 225 none)) = d5559 p
  rw [sub9655, sub9637]
  rfl
theorem sub9657 (p : Pattern) : d2539 (change p 225 none) = d5560 p := by
  change (if p 161 then d2538 (change p 225 none) else d2529 (change p 225 none)) = d5560 p
  rw [sub9656, sub9638]
  rfl
theorem sub9658 (p : Pattern) : d31 (change p 225 none) = d31 p := by
  change (if p 246 then d30 (change p 225 none) else d2 (change p 225 none)) = d31 p
  rw [sub9607, sub9605]
  rfl
theorem sub9659 (p : Pattern) : d2540 (change p 225 none) = d31 p := by
  change d31 (change p 225 none) = d31 p
  exact sub9658 p
theorem sub9660 (p : Pattern) : d1713 (change p 225 none) = d1713 p := by
  change (if p 247 then d6 (change p 225 none) else d2 (change p 225 none)) = d1713 p
  rw [sub9629, sub9605]
  rfl
theorem sub9661 (p : Pattern) : d1714 (change p 225 none) = d1714 p := by
  change (if p 246 then d34 (change p 225 none) else d1713 (change p 225 none)) = d1714 p
  rw [sub9631, sub9660]
  rfl
theorem sub9662 (p : Pattern) : d2541 (change p 225 none) = d1714 p := by
  change d1714 (change p 225 none) = d1714 p
  exact sub9661 p
theorem sub9663 (p : Pattern) : d2542 (change p 225 none) = d5561 p := by
  change (if p 224 then d2541 (change p 225 none) else d2540 (change p 225 none)) = d5561 p
  rw [sub9662, sub9659]
  rfl
theorem sub9664 (p : Pattern) : d2543 (change p 225 none) = d5562 p := by
  change (if p 204 then d12 (change p 225 none) else d2542 (change p 225 none)) = d5562 p
  rw [sub9592, sub9663]
  rfl
theorem sub9665 (p : Pattern) : d2544 (change p 225 none) = d5563 p := by
  change (if p 182 then d2543 (change p 225 none) else d2518 (change p 225 none)) = d5563 p
  rw [sub9664, sub9618]
  rfl
theorem sub9666 (p : Pattern) : d35 (change p 225 none) = d35 p := by
  change (if p 246 then d34 (change p 225 none) else d6 (change p 225 none)) = d35 p
  rw [sub9631, sub9629]
  rfl
theorem sub9667 (p : Pattern) : d2545 (change p 225 none) = d35 p := by
  change d35 (change p 225 none) = d35 p
  exact sub9666 p
theorem sub9668 (p : Pattern) : d10 (change p 225 none) = d10 p := by
  rfl
theorem sub9669 (p : Pattern) : d1721 (change p 225 none) = d1721 p := by
  change (if p 247 then d10 (change p 225 none) else d6 (change p 225 none)) = d1721 p
  rw [sub9668, sub9629]
  rfl
theorem sub9670 (p : Pattern) : d57 (change p 225 none) = d57 p := by
  change (if p 247 then d12 (change p 225 none) else d10 (change p 225 none)) = d57 p
  rw [sub9592, sub9668]
  rfl
theorem sub9671 (p : Pattern) : d1722 (change p 225 none) = d1722 p := by
  change (if p 246 then d57 (change p 225 none) else d1721 (change p 225 none)) = d1722 p
  rw [sub9670, sub9669]
  rfl
theorem sub9672 (p : Pattern) : d2546 (change p 225 none) = d1722 p := by
  change d1722 (change p 225 none) = d1722 p
  exact sub9671 p
theorem sub9673 (p : Pattern) : d2547 (change p 225 none) = d5564 p := by
  change (if p 224 then d2546 (change p 225 none) else d2545 (change p 225 none)) = d5564 p
  rw [sub9672, sub9667]
  rfl
theorem sub9674 (p : Pattern) : d2548 (change p 225 none) = d5565 p := by
  change (if p 204 then d12 (change p 225 none) else d2547 (change p 225 none)) = d5565 p
  rw [sub9592, sub9673]
  rfl
theorem sub9675 (p : Pattern) : d2549 (change p 225 none) = d5566 p := by
  change (if p 182 then d2548 (change p 225 none) else d2518 (change p 225 none)) = d5566 p
  rw [sub9674, sub9618]
  rfl
theorem sub9676 (p : Pattern) : d2550 (change p 225 none) = d5567 p := by
  change (if p 163 then d2549 (change p 225 none) else d2544 (change p 225 none)) = d5567 p
  rw [sub9675, sub9665]
  rfl
theorem sub9677 (p : Pattern) : d40 (change p 225 none) = d40 p := by
  change (if p 246 then d39 (change p 225 none) else d11 (change p 225 none)) = d40 p
  rw [sub9649, sub9647]
  rfl
theorem sub9678 (p : Pattern) : d2551 (change p 225 none) = d40 p := by
  change d40 (change p 225 none) = d40 p
  exact sub9677 p
theorem sub9679 (p : Pattern) : d327 (change p 225 none) = d327 p := by
  change (if p 246 then d12 (change p 225 none) else d39 (change p 225 none)) = d327 p
  rw [sub9592, sub9649]
  rfl
theorem sub9680 (p : Pattern) : d332 (change p 225 none) = d327 p := by
  change d327 (change p 225 none) = d327 p
  exact sub9679 p
theorem sub9681 (p : Pattern) : d2552 (change p 225 none) = d5568 p := by
  change (if p 224 then d332 (change p 225 none) else d2551 (change p 225 none)) = d5568 p
  rw [sub9680, sub9678]
  rfl
theorem sub9682 (p : Pattern) : d2553 (change p 225 none) = d5569 p := by
  change (if p 204 then d12 (change p 225 none) else d2552 (change p 225 none)) = d5569 p
  rw [sub9592, sub9681]
  rfl
theorem sub9683 (p : Pattern) : d2554 (change p 225 none) = d5570 p := by
  change (if p 182 then d2553 (change p 225 none) else d2518 (change p 225 none)) = d5570 p
  rw [sub9682, sub9618]
  rfl
theorem sub9684 (p : Pattern) : d2555 (change p 225 none) = d5571 p := by
  change (if p 182 then d12 (change p 225 none) else d2523 (change p 225 none)) = d5571 p
  rw [sub9592, sub9628]
  rfl
theorem sub9685 (p : Pattern) : d2556 (change p 225 none) = d5572 p := by
  change (if p 163 then d2555 (change p 225 none) else d2554 (change p 225 none)) = d5572 p
  rw [sub9684, sub9683]
  rfl
theorem sub9686 (p : Pattern) : d2557 (change p 225 none) = d5573 p := by
  change (if p 162 then d2556 (change p 225 none) else d2550 (change p 225 none)) = d5573 p
  rw [sub9685, sub9676]
  rfl
theorem sub9687 (p : Pattern) : d2558 (change p 225 none) = d5574 p := by
  change (if p 182 then d12 (change p 225 none) else d2518 (change p 225 none)) = d5574 p
  rw [sub9592, sub9618]
  rfl
theorem sub9688 (p : Pattern) : d2559 (change p 225 none) = d5575 p := by
  change (if p 163 then d2555 (change p 225 none) else d2558 (change p 225 none)) = d5575 p
  rw [sub9684, sub9687]
  rfl
theorem sub9689 (p : Pattern) : d2560 (change p 225 none) = d5576 p := by
  change (if p 182 then d12 (change p 225 none) else d2532 (change p 225 none)) = d5576 p
  rw [sub9592, sub9646]
  rfl
theorem sub9690 (p : Pattern) : d2561 (change p 225 none) = d5577 p := by
  change (if p 163 then d12 (change p 225 none) else d2560 (change p 225 none)) = d5577 p
  rw [sub9592, sub9689]
  rfl
theorem sub9691 (p : Pattern) : d2562 (change p 225 none) = d5578 p := by
  change (if p 162 then d2561 (change p 225 none) else d2559 (change p 225 none)) = d5578 p
  rw [sub9690, sub9688]
  rfl
theorem sub9692 (p : Pattern) : d2563 (change p 225 none) = d5579 p := by
  change (if p 161 then d2562 (change p 225 none) else d2557 (change p 225 none)) = d5579 p
  rw [sub9691, sub9686]
  rfl
theorem sub9693 (p : Pattern) : d2564 (change p 225 none) = d5580 p := by
  change (if p 160 then d2563 (change p 225 none) else d2539 (change p 225 none)) = d5580 p
  rw [sub9692, sub9657]
  rfl
theorem sub9694 (p : Pattern) : d2565 (change p 225 none) = d14 p := by
  change d14 (change p 225 none) = d14 p
  exact sub9594 p
theorem sub9695 (p : Pattern) : d2566 (change p 225 none) = d14 p := by
  change (if p 224 then d2504 (change p 225 none) else d2565 (change p 225 none)) = d14 p
  rw [sub9596, sub9694]
  simp only [ite_self]
theorem sub9696 (p : Pattern) : d2567 (change p 225 none) = d5542 p := by
  change (if p 204 then d2507 (change p 225 none) else d2566 (change p 225 none)) = d5542 p
  rw [sub9603, sub9695]
  rfl
theorem sub9697 (p : Pattern) : d2568 (change p 225 none) = d5545 p := by
  change (if p 182 then d2511 (change p 225 none) else d2567 (change p 225 none)) = d5545 p
  rw [sub9611, sub9696]
  rfl
theorem sub9698 (p : Pattern) : d2569 (change p 225 none) = d5581 p := by
  change (if p 204 then d2542 (change p 225 none) else d2540 (change p 225 none)) = d5581 p
  rw [sub9663, sub9659]
  rfl
theorem sub9699 (p : Pattern) : d1742 (change p 225 none) = d1742 p := by
  change (if p 247 then d4 (change p 225 none) else d2 (change p 225 none)) = d1742 p
  rw [sub9598, sub9605]
  rfl
theorem sub9700 (p : Pattern) : d1743 (change p 225 none) = d1743 p := by
  change (if p 246 then d17 (change p 225 none) else d1742 (change p 225 none)) = d1743 p
  rw [sub9600, sub9699]
  rfl
theorem sub9701 (p : Pattern) : d2570 (change p 225 none) = d1743 p := by
  change d1743 (change p 225 none) = d1743 p
  exact sub9700 p
theorem sub9702 (p : Pattern) : d2571 (change p 225 none) = d5582 p := by
  change (if p 224 then d2570 (change p 225 none) else d2540 (change p 225 none)) = d5582 p
  rw [sub9701, sub9659]
  rfl
theorem sub9703 (p : Pattern) : d2572 (change p 225 none) = d5583 p := by
  change (if p 204 then d12 (change p 225 none) else d2571 (change p 225 none)) = d5583 p
  rw [sub9592, sub9702]
  rfl
theorem sub9704 (p : Pattern) : d2573 (change p 225 none) = d5584 p := by
  change (if p 182 then d2572 (change p 225 none) else d2569 (change p 225 none)) = d5584 p
  rw [sub9703, sub9698]
  rfl
theorem sub9705 (p : Pattern) : d2574 (change p 225 none) = d5585 p := by
  change (if p 163 then d2573 (change p 225 none) else d2568 (change p 225 none)) = d5585 p
  rw [sub9704, sub9697]
  rfl
theorem sub9706 (p : Pattern) : d2575 (change p 225 none) = d5586 p := by
  change (if p 163 then d2536 (change p 225 none) else d2527 (change p 225 none)) = d5586 p
  rw [sub9654, sub9636]
  rfl
theorem sub9707 (p : Pattern) : d2576 (change p 225 none) = d5587 p := by
  change (if p 162 then d2575 (change p 225 none) else d2574 (change p 225 none)) = d5587 p
  rw [sub9706, sub9705]
  rfl
theorem sub9708 (p : Pattern) : d58 (change p 225 none) = d58 p := by
  change (if p 246 then d57 (change p 225 none) else d10 (change p 225 none)) = d58 p
  rw [sub9670, sub9668]
  rfl
theorem sub9709 (p : Pattern) : d2577 (change p 225 none) = d58 p := by
  change d58 (change p 225 none) = d58 p
  exact sub9708 p
theorem sub9710 (p : Pattern) : d329 (change p 225 none) = d329 p := by
  change (if p 246 then d12 (change p 225 none) else d57 (change p 225 none)) = d329 p
  rw [sub9592, sub9670]
  rfl
theorem sub9711 (p : Pattern) : d330 (change p 225 none) = d329 p := by
  change d329 (change p 225 none) = d329 p
  exact sub9710 p
theorem sub9712 (p : Pattern) : d2578 (change p 225 none) = d5588 p := by
  change (if p 224 then d330 (change p 225 none) else d2577 (change p 225 none)) = d5588 p
  rw [sub9711, sub9709]
  rfl
theorem sub9713 (p : Pattern) : d2579 (change p 225 none) = d5589 p := by
  change (if p 204 then d2578 (change p 225 none) else d2577 (change p 225 none)) = d5589 p
  rw [sub9712, sub9709]
  rfl
theorem sub9714 (p : Pattern) : d2580 (change p 225 none) = d5590 p := by
  change (if p 204 then d12 (change p 225 none) else d2578 (change p 225 none)) = d5590 p
  rw [sub9592, sub9712]
  rfl
theorem sub9715 (p : Pattern) : d2581 (change p 225 none) = d5591 p := by
  change (if p 182 then d2580 (change p 225 none) else d2579 (change p 225 none)) = d5591 p
  rw [sub9714, sub9713]
  rfl
theorem sub9716 (p : Pattern) : d2582 (change p 225 none) = d5592 p := by
  change (if p 163 then d2581 (change p 225 none) else d2527 (change p 225 none)) = d5592 p
  rw [sub9715, sub9636]
  rfl
theorem sub9717 (p : Pattern) : d2583 (change p 225 none) = d5593 p := by
  change (if p 204 then d2552 (change p 225 none) else d2551 (change p 225 none)) = d5593 p
  rw [sub9681, sub9678]
  rfl
theorem sub9718 (p : Pattern) : d2584 (change p 225 none) = d5594 p := by
  change (if p 182 then d2553 (change p 225 none) else d2583 (change p 225 none)) = d5594 p
  rw [sub9682, sub9717]
  rfl
theorem sub9719 (p : Pattern) : d2585 (change p 225 none) = d5595 p := by
  change (if p 163 then d12 (change p 225 none) else d2584 (change p 225 none)) = d5595 p
  rw [sub9592, sub9718]
  rfl
end NetHack.Sokoban22Refined85
