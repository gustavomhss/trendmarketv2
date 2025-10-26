import os
import sys
from pathlib import Path

ROOT_DIR = Path(__file__).resolve().parents[1]
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from hypothesis import settings


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
