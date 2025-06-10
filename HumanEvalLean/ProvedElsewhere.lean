/-- This is an axiom used by `human-eval-lean` for statements whose proof is present in a library
like `Batteries` or `mathlib`. The location parameter should be filled with a link to the file or
PR containing the proof. This axiom is a last resort, it is preferable to copy the proof into
the `human-eval-lean` file instead. -/
axiom proved_elsewhere {α : Prop} (location : String) : α
