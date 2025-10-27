import os
import sys
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parents[1]
SRC_DIR = ROOT_DIR / "src"

if SRC_DIR.exists():
    src_path = str(SRC_DIR)
    if src_path not in sys.path:
        sys.path.insert(0, src_path)

root_path = str(ROOT_DIR)
if root_path not in sys.path:
    sys.path.append(root_path)

from hypothesis import settings  # noqa: E402

settings.register_profile(
    "ci",
    max_examples=200,
    deadline=None,
    print_blob=True,
)
settings.register_profile(
    "dev",
    max_examples=25,
    deadline=None,
)
settings.load_profile(os.getenv("HYPOTHESIS_PROFILE", "dev"))
