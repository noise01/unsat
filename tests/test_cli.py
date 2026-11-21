import subprocess
import sys
import sysconfig
from pathlib import Path


def test_unsat_starts():
    command = Path(sysconfig.get_path("scripts")) / "unsat"
    result = subprocess.run([command], check=True, capture_output=True, text=True)

    assert result.stdout.strip() == "Hello from unsat!"


def test_python_m_unsat_starts():
    result = subprocess.run(
        [sys.executable, "-m", "unsat"],
        check=True,
        capture_output=True,
        text=True,
    )

    assert result.stdout.strip() == "Hello from unsat!"
