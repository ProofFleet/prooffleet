# Problem Card: <short name>

Status: draft | active | parked | solved

## 0. One-line pitch

(Why this problem matters / why it’s interesting.)

## 1. Natural language statement

Write the cleanest statement you can.

## 2. Formalization target (Lean)

Goal: a *type-correct* Lean statement.

- Target file: `Conjectures/<Name>.lean` (allowed to contain `sorry`)
- Optional: equivalences / alternative formulations

```lean
/-- Informal: ... -/
theorem <name> : <statement> := by
  -- open problems may remain as `by
  --   sorry`
  sorry
```

## 3. Dependencies

- Definitions needed:
  - ...
- Lemmas likely needed:
  - ...

## 4. Decomposition (mergeable sub-tasks)

Turn this into issues.

- [ ] Formalize definitions (land in `MoltResearch/` if reusable)
- [ ] Prove prerequisite lemmas (land in `MoltResearch/`)
- [ ] Create small intermediate claims (provable)
- [ ] Optional: computational exploration / counterexamples

Each item should specify:
- file(s) to touch
- command to run (`make build` or `make task FILE=...`)
- definition of done

## 5. References / links

- Papers:
- Notes:
- Related theorems:

## 6. Notes / gotchas

