import Lake
open Lake DSL

-- Keep this revision in step with the Aeneas binary used by
-- scripts/extract-lean.sh: the generated code targets its Lean library.
require aeneas from git
  "https://github.com/AeneasVerif/aeneas.git" @ "b434e6e83413c88a359dd15a2068885ccc4744c2" / "backends/lean"

package «cobblestone»

@[default_target] lean_lib «Cobblestone»
