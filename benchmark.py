import json
import subprocess
import sys
import time
from pathlib import Path

THEOREMS = [
    ("Mathlib/Data/Nat/Basic.lean",        "Nat.add_comm"),
    ("Mathlib/Data/Nat/Basic.lean",        "Nat.add_zero"),
    ("Mathlib/Data/Nat/Basic.lean",        "Nat.mul_comm"),
    ("Mathlib/Data/Nat/Basic.lean",        "Nat.zero_add"),
    ("Mathlib/Data/List/Basic.lean",       "List.length_append"),
    ("Mathlib/Data/List/Basic.lean",       "List.reverse_reverse"),
    ("Mathlib/Algebra/Group/Basic.lean",   "mul_one"),
    ("Mathlib/Algebra/Group/Basic.lean",   "one_mul"),
]

MAX_ITERATIONS = 50
TIMEOUT = 120  # seconds per theorem

Path("outputs").mkdir(exist_ok=True)

results = []
print(f"\nRunning {len(THEOREMS)} theorems  (timeout={TIMEOUT}s each)\n")
print(f"{'Theorem':<35} {'Result':<10} {'Time':>6}")
print("-" * 55)

for file_path, thm in THEOREMS:
    metrics_out = f"outputs/{thm.replace('.', '_')}.json"
    t0 = time.time()

    proc = subprocess.run(
        [
            sys.executable, "-m", "hybrid_atp.cli",
            "--file", file_path,
            "--theorem", thm,
            "--max-iterations", str(MAX_ITERATIONS),
            "--timeout", str(TIMEOUT),
            "--metrics-path", metrics_out,
            "--log-level", "WARNING",
        ],
        capture_output=True,
        text=True,
    )

    elapsed = time.time() - t0
    success = proc.returncode == 0
    symbol = "✔  PROVED" if success else "✘  failed"
    print(f"{thm:<35} {symbol:<10} {elapsed:>5.1f}s")

    results.append({
        "theorem": thm,
        "file": file_path,
        "success": success,
        "wall_seconds": round(elapsed, 1),
        "metrics_file": metrics_out,
        "stderr_tail": proc.stderr[-300:] if proc.stderr else "",
    })

passed = sum(r["success"] for r in results)
total = len(results)
print("-" * 55)
print(f"\nResult: {passed}/{total} proved  ({100*passed//total}%)\n")

summary_path = Path("outputs/benchmark_summary.json")
summary_path.write_text(json.dumps(results, indent=2))
print(f"Full results written to {summary_path}")
