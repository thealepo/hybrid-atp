# Validation Feature Guide

The system now supports **validating tactics in Lean 4**! This means you can see if the generated tactics actually work.

## How to Use Validation

### Step 1: Install lean-dojo
```bash
pip install lean-dojo>=1.8.0
```

### Step 2: Run the web app
```bash
python app.py
```

### Step 3: In the web interface

1. Enter your theorem statement (or use an example)
2. Check the **"Validate tactics in Lean"** checkbox
3. Fill in the required fields:
   - **Lean File Path**: e.g., `Mathlib/Data/List/Basic.lean`
   - **Theorem Name**: e.g., `List.reverse_append`
4. Click **"Generate Strategy"**

### What You'll See

Each generated tactic will show:

- **✓ VALID** - Tactic executed successfully
  - Shows the next proof state
  - Click "Show next state" to see what remains to prove

- **✓ PROOF COMPLETE** - Tactic finished the proof!
  - The theorem is fully proved

- **✗ INVALID** - Tactic failed
  - Shows the error message from Lean
  - Helps you understand why it didn't work

## Example

**Input:**
- Lean File: `Mathlib/Data/List/Basic.lean`
- Theorem: `List.reverse_append`
- Statement: `⊢ ∀ (xs ys : List α), reverse (xs ++ ys) = reverse ys ++ reverse xs`

**Output:**
```
Tactic 1: intro xs ys              ✓ VALID
  → Tactic succeeded
  → Next state: ⊢ reverse (xs ++ ys) = reverse ys ++ reverse xs

Tactic 2: induction xs              ✓ VALID
  → Tactic succeeded
  → Next state: [Shows induction cases]

Tactic 3: simp [*]                  ✗ INVALID
  → Error: tactic 'simp' failed...
```

## Important Notes

### Validation Requirements
- **Lean file must exist** in Mathlib4 repository
- **Theorem must be defined** in that file
- First run downloads Mathlib4 (~1GB) - may take time
- Subsequent runs are faster (uses cache)

### Performance
- Validation adds 5-30 seconds depending on theorem complexity
- Lean initialization happens once per theorem
- Multiple tactics are validated sequentially

### Without Validation
If you uncheck "Validate tactics in Lean":
- Tactics are generated but NOT tested
- Much faster (no Lean overhead)
- Good for exploration and learning

## Troubleshooting

**Error: "Failed to initialize Lean environment"**
- Check file path is correct (e.g., `Mathlib/Data/List/Basic.lean`)
- Check theorem name matches exactly (case-sensitive)
- Ensure lean-dojo is installed

**Slow first run**
- LeanDojo downloads Mathlib4 on first use
- This is normal and only happens once
- Subsequent runs use cached data

**All tactics show INVALID**
- The LLM suggestions may not be perfect
- Try different theorems
- Use this to learn what works and what doesn't!
