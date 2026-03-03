---
name: restructure-solutions
description: Restructures a Lean file with one or many solution implementations so that each solution is self-contained with its own Implementation, Tests, and Verification sections.
---

# Restructure Solutions

This skill takes a Lean file of a human-eval problem that has multiple solution variants (like `solution`, `solution'`, `solution''`) and restructures it so that:

1. Each solution gets its own section group:
   - `## Implementation`
   - `## Tests`
   - `## Missing API` (only if there are any lemmas/attributes/... that were added because they are missing in the standard library; usually those prefixed with `List`, `Nat`, etc.)
   - `## Verification`
   If there are many solutions, these three sections exist for every solution and are numbered.

2. Solutions are no longer interleaved - each is completely self-contained

3. The original Prompt section (if present) is preserved at the end

## Examples

**Single solution before:**
```lean
def solution := ...

example : solution ... := ...

theorem solution_spec := ...
```

**Single solution after:**
```lean
## Implementation
def solution := ...

## Tests
example : solution ... := ...

## Verification
theorem solution_spec := ...
```

**Multiple solutions before:**
```lean
def solution := ...
def solution' := ...
def solution'' := ...

example : solution ... := ...
example : solution' ... := ...
example : solution'' ... := ...

theorem solution_spec := ...
theorem solution'_spec := ...
```

**Multiple solutions after:**
```lean
## Implementation 1
def solution := ...

## Tests 1
example : solution ... := ...

## Verification 1
theorem solution_spec := ...

## Implementation 2
def solution' := ...

## Tests 2
example : solution' ... := ...

## Verification 2
theorem solution'_spec := ...

## Implementation 3
def solution'' := ...

## Tests 3
example : solution'' ... := ...

## Verification 3
...
```

## Instructions for Claude

1. Read the file specified by the user
2. Identify all solution definitions (typically named according to the function in the prompt at the end of the file)
3. For each solution variant:
   - Extract the implementation definition
   - Extract all test examples that reference that solution
   - Extract all verification theorems/lemmas that reference that solution
   - Group them into sections that are numbered ONLY IF there is more than one solution (Implementation N, Tests N, Verification N)
4. Preserve any helper lemmas/theorems in the Verification section where they're first needed
5. Keep the Prompt section (and Canonical solution, Tests sections) at the very end, unchanged
6. Maintain all imports, opens, and options at the top of the file
7. Use the Edit tool to restructure the file with the new organization
8. Double-check that you have added the necessary tests

## Notes

- Use the `cbv` tactic for tests when possible. It might fail to reduce some special constructs.
- If `cbv` fails, use `decide` (for simple recursive functions or monadic code) or `native_decide`
  (for tests involving iterators or complex computations that don't reduce well).
- If you use `cbv`, use `set_option cbv.warning false`.
- Preserve all comments, attributes, and proof code exactly as they are
- Helper lemmas that are used across multiple solutions should stay in the first Verification section where they appear
- Problem number X can be found in `HumanEvalLean/HumanEvalX.lean`
- If in doubt, check `HumanEvalLean/HumanEval114.lean` for a reference
