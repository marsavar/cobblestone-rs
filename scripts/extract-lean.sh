#!/usr/bin/env bash
# Regenerates the Lean model of the chunk layer (src/raw.rs), the header
# (src/header.rs) and the stream buffering (src/buffer.rs) in lean/Cobblestone.
#
# Charon and Aeneas come from the Aeneas flake, pinned to the same revision as
# the Aeneas Lean library in lean/lakefile.lean. Aeneas only accepts LLBC from
# the Charon it was built with, so both must come from this one flake.
set -euo pipefail

AENEAS_REV=b434e6e83413c88a359dd15a2068885ccc4744c2

root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

nix shell "github:AeneasVerif/aeneas/$AENEAS_REV#aeneas" --command bash -euo pipefail -c '
  root=$1 work=$2
  cd "$root"
  charon cargo --preset aeneas \
    --start-from "crate::raw" --start-from "crate::header" --start-from "crate::buffer" --exclude "crate::raw::tests" \
    --dest-file "$work/cobblestone.llbc" -- --features cobblestone-256
  aeneas -backend lean -split-files -abort-on-error -warnings-as-errors -no-progress-bar \
    -dest "$work/lean" "$work/cobblestone.llbc"
' _ "$root" "$work"

# FunsExternal.lean holds hand-written definitions for the externals listed in
# the template, so only the template is replaced; diff it against
# FunsExternal.lean to see if an external was added or removed.
cp "$work/lean/Types.lean" "$work/lean/Funs.lean" "$root/lean/Cobblestone/"
cp "$work/lean/FunsExternal_Template.lean" "$root/lean/Cobblestone/"
