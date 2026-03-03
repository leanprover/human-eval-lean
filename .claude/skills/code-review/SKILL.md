---
name: code-review
description: Performs thorough code reviews of individual human-eval problems.  Use when asked explicity to review code or analyze code quality.
---

# Code Review

Conduct systematic, thorough code reviews that examine multiple dimensions of code quality.

## Review Process

Review the human-eval problem/solution the user told you to review. The purpose of the solution is to assess and showcase Lean's aptitude for writing an verifying everyday programming tasks. The solutions should be understandable for outsiders that have not done much work in Lean and ideally convince them that Lean is a good choice for writing and verifying software. In the best case, the elegance and simplicity of the solutions enabled by Lean should baffle them.

A second purpose is that implementing these solutions will turn up missing API and API defects in the standard library.

### 1. **Understand the Context**
- Read the whole file that contains the problem. Note that the prompt at the end of the file has been given and is relevant context but not subject of the review itself.
- Ask questions if needed.

### 2. **File Structure**

Check that the file follows the project's structural conventions:

- **Section organization**: Are the standard sections present and in the correct order?
  - Implementation section: `/-! ## Implementation -/`
  - Tests section: `/-! ## Tests -/`
  - Missing API section (if needed): `/-! ## Missing API -/`
  - Verification section: `/-! ## Verification -/`
  - Prompt section: `/-! ## Prompt ... -/` (auto-generated, immutable)
  Notable exception: If the implementation depends on declarations from the Missing API section, then the Missing API section naturally comes first.

- **Missing API lemmas**: This is a key structural requirement. Helper lemmas that would naturally belong in Lean's standard library MUST be:
  - Placed in a dedicated `/-! ## Missing API -/` section (typically between Tests and Verification)
  - Properly namespaced with standard library types (e.g., `List.someHelper`, `Nat.someProperty`, `Array.someTheorem`)
  - Look specifically for lemmas about `List`, `Array`, `Nat`, `String`, `Option`, and other core types
  - This documentation is essential for identifying gaps in Lean's out-of-the-box verification capabilities

- **Section headers**: Are all major sections clearly marked with `/-! ## Section Name -/`?

- **Subsections**: Within Verification, are there helpful subsections (e.g., `/-! ### Loop invariants -/`, `/-! ### Main theorems -/`) that guide the reader?

### 3. **Documentation and Narrative**

- **Module docstrings**: Does the file have clear section headers (`/-! ... -/`) that guide the reader through the solution?
- **Narrative flow**: Do the docstrings create a coherent story from problem statement → preliminaries → implementation → tests → verification?
- **Section ordering**: Are sections presented in a logical learning order (e.g., simpler approaches before complex ones)?
- **Pedagogical clarity**: Would a reader unfamiliar with the codebase understand the approach and motivation?
- **Redundancy**: Are there redundant or contradictory explanations across different docstrings?
- **Completeness**: Are key design decisions, trade-offs, or unusual techniques explained?

### 4. **Style and readability**

- Do the changes adhere to [standard library style](https://github.com/leanprover/lean4/blob/master/doc/std/style.md)?
- **Naming**: Are variable/function names clear and descriptive?
- **Structure**: Is the code organized logically? Are functions too large? Is the file structured in a way that lends itself to a single comfortable read-through?
- **Comments**: Are complex sections explained? Are comments accurate?
- **Consistency**: Does code follow the project's conventions?
- **Clarity**: Could an outsider that has worked with other theorem provers before understand the code, or at least what it does, quickly?
- **Design**: Is the implementation and verification approach appropriate? Are there simpler solutions?

**Lemma style guidelines**

- Are the lemmas' names consistent and descriptive?
- Do the lemmas' names adhere to the [naming convention](https://github.com/leanprover/lean4/blob/master/doc/std/naming.md)?
- Do the lemmas avoid non-terminal `simp` and `simp_all`? Note: `simp only` and `simp_all only` is fine, `simp; omega` too.
- Are lemma arguments implicit where this makes sense?

### 5. **Correctness**

- Are there tests for the Lean implementation? Do the tests match the tests in the prompt sections?
- Does the solution actually solve the problem in the prompt as instructed?
- Do the verification lemmas (excluding lemmas that are pure helpers with technical and difficult statements) uniquely determine the solution's behavior?
- Are the lemmas that seem to be intended as missing API plausible and consistent additions to Lean's standard library?
- Does the code avoid using `sorry` and `admit`?
- Check terminology, grammar and orthography (function names, variable names, comments, docstrings)

**CRITICAL: Semantic Interpretation & Verification Gaps**

This is one of the most important aspects of the review. Carefully examine whether the formal specification matches the informal prompt:

- **Semantic mismatches**: Does the formalization interpret the problem differently than the prompt describes it? Examples:
  - Prompt says "closed intervals [a, b]" but code uses half-open ranges [a, b)
  - Prompt says "length" meaning element count but code computes difference
  - Prompt says "empty list" but code uses Option.none
  - Prompt describes 1-indexed positions but code uses 0-indexed

- **Undocumented semantic choices**: Even if the formalization is mathematically equivalent, are non-obvious interpretation choices explained? A reader should understand:
  - Why a particular data structure was chosen
  - How the formal model relates to the informal description
  - What assumptions or simplifications were made

- **Verification gap**: Is there a gap between what the prompt asks for and what the theorems prove? Could a bug hide in this gap?

- **Severity guidelines for semantic issues**:
  - **High**: Semantic mismatch that could hide bugs or make verification meaningless (e.g., proving properties of the wrong data structure)
  - **Medium**: Undocumented semantic choice that works correctly but would confuse readers unfamiliar with the approach
  - **Low**: Minor interpretation difference that's obvious from context

When you find semantic interpretation differences, ALWAYS classify them under "Correctness/Verification Gaps" in your review, not under "Design" or other categories.

### 6. **Performance and Efficiency**

Solutions should be reasonably efficient.

- **Algorithms**: Are appropriate algorithms used? Any O(n²) where O(n) is possible?
- **Resource usage**: Are resources allocated and freed properly?
- **Redundancy**: Is there unnecessary duplication or recomputation?

### 7. **Overall rating**

Evaluate how well the solution, and its verification, match their purpose of being compelling examples of simple execution and formal verification of small programming tasks.

## Review Structure

Present your review organized by category:

```markdown
## Summary
Brief overview of the changes and overall assessment.

## ✅ Strengths
What the code does well.

## 🔍 Issues Found

### File Structure
- [Severity] Description (missing sections, missing API not separated, incorrect section ordering)

### Correctness/Verification Gaps
- [Severity] Description (semantic mismatches, undocumented interpretation choices, verification gaps)

### Documentation
- [Severity] Description (unclear section headers, poor narrative flow, redundant explanations)

### Style/Readability
- [Severity] Description

### Performance
- [Severity] Description

### Design
- [Severity] Description

## 🤔 Questions
Clarifications needed about intent or design decisions.

## 📋 Suggestions (Optional)
Nice-to-haves that aren't blocking.

## Overall Assessment
Final recommendation: Approve / Request Changes / Comment
```

## Severity Levels

- **Critical**: Causes incorrect behavior, security vulnerability, data loss, or completely invalidates the verification
- **High**:
  - Semantic mismatches between prompt and formalization that could hide bugs
  - Significant verification gaps where theorems don't prove what the prompt asks
  - Significant design flaws or performance issues
  - Maintainability concerns
  - Missing API lemmas not separated into their own section
- **Medium**:
  - Undocumented semantic interpretation choices that work correctly but confuse readers
  - Code quality issues or readability problems
  - Non-obvious bugs
  - Missing or unclear section headers
- **Low**:
  - Minor style issues
  - Documentation improvements
  - Suggestions for enhancement

## Tips for Effective Reviews

1. **Be constructive**: Focus on the code, not the person. Use "this could be clearer" not "you wrote this unclearly"
3. **Ask questions**: If you don't understand, ask. That's a code clarity issue
5. **Know when to stop**: Don't demand perfection; distinguish between blocking and nice-to-have
6. **Reference standards**: Point to style guides, documentation, or existing patterns when suggesting changes
7. **Test mentally**: Walk through the code with example inputs to catch edge cases *where appropriate*
8. **Read as a newcomer**: When reviewing documentation, imagine you're encountering the code for the first time. Are section headers clear? Does the narrative flow? Would you understand the motivation and approach?
9. **Check file structure first**: Before diving into code details, verify the file has the correct sections in the right order, and that missing API lemmas are properly separated.
10. **Scrutinize semantics**: Always read the prompt carefully and compare it line-by-line with the formalization. Look for:
   - Different data structure interpretations (arrays vs lists, closed vs half-open intervals)
   - Different counting conventions (0-indexed vs 1-indexed, inclusive vs exclusive)
   - Different notions of "length", "size", "count", "empty", etc.
   - Any implicit assumptions in the formalization not stated in the prompt
   Even if mathematically equivalent, these differences should be documented and flagged appropriately.
