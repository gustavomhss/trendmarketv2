import json
import subprocess
import tempfile
from pathlib import Path
from unittest import TestCase

from amm_obs.sbom import generate_sbom


class SBOMGenerationTests(TestCase):
    def setUp(self) -> None:
        result = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        )
        self.commit = result.stdout.strip()

    def test_generate_sbom_creates_cyclonedx_payload(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "sbom.cdx.json"
            bom = generate_sbom(output)

            self.assertTrue(output.exists(), "SBOM file should be written to disk")
            self.assertEqual("CycloneDX", bom["bomFormat"])
            self.assertEqual(self.commit, bom["metadata"]["component"]["version"])
            self.assertEqual(1, bom["version"])
            self.assertTrue(bom["dependencies"], "Dependencies array should contain the root component")

            with output.open("r", encoding="utf-8") as handle:
                round_trip = json.load(handle)
            self.assertEqual(bom, round_trip)

    def test_serial_number_is_deterministic(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "sbom.cdx.json"
            bom_one = generate_sbom(output)
            bom_two = generate_sbom(output)

        self.assertEqual(bom_one["serialNumber"], bom_two["serialNumber"])
        self.assertTrue(bom_one['serialNumber'].startswith('urn:uuid:'), 'serialNumber must include urn:uuid prefix')
