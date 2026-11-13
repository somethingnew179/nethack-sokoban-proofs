# Notice and attribution

This repository packages Lean 4 proofs about the Sokoban levels of NetHack.

**NetHack.** The eight files `dat/soko*-*.lua` are unmodified copies from NetHack,
<https://github.com/NetHack/NetHack.git>, commit
`b0c09c878e1f9f62bc7ab20e6edafd6108c325a0`. `lean/NetHack/Sokoban/Maps.lean` is
generated from them. NetHack is Copyright 1985-2026 by Stichting Mathematisch
Centrum and M. Stephenson and is distributed under the NetHack General Public
License, reproduced unchanged in `LICENSE` (identical to upstream `dat/license`).

**Lean proof sources.** Everything under `lean/NetHack/` is copied byte for byte
from the private development tree of the NetHack Lean port at the same relative
path. NetHack-derived code follows `LICENSE`. No other licence is granted by this
package for the remaining proof code; the owner decides that before any publication.

**Added for this package.** `lean/Audit/`, `lean/lakefile.toml`, `roots.json`,
`scripts/`, `MANIFEST.sha256`, the README, this notice and the
verification receipts. The Lean core library and toolchain (`leanprover/lean4`
v4.33.1) are not copied here.
