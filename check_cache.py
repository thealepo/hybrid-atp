from pathlib import Path

URL = "https://github.com/leanprover-community/mathlib4"
COMMIT = "4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84"


slug = URL.replace("https://", "").replace("/", "-").replace(".", "-")
folder_name = f"{slug}-{COMMIT}"
cache_path = Path.home() / ".cache" / "lean_dojo" / "repos" / folder_name

print(f"\nChecking for: {folder_name}")
print(f"Looking in: {cache_path}")

if cache_path.exists():
    print("\nSUCCESS: Cache folder found")

    if (cache_path / "lake-packages").exists():
        print("SUCCESS: Dependencies found")
        print("\nSAFE TO RUN MAIN.PY. It will skip download.")
    else:
        print("WARNING: Folder exists but dependencies are missing")
else:
    print("\nDANGER: Python cannot find the folder")