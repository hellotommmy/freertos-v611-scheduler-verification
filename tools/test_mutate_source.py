import tempfile
import unittest
from pathlib import Path

from mutate_source import create_mutant


class MutateSourceTests(unittest.TestCase):
    def test_named_mutation_requires_and_replaces_one_anchor(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "list.c"
            destination = root / "mutant.c"
            source.write_text(
                "void f(void) {\n"
                "\tpxItemToRemove->pxNext->pxPrevious = pxItemToRemove->pxPrevious;\n"
                "}\n",
                encoding="utf-8",
            )
            manifest = create_mutant(source, destination, "drop-remove-reverse-link")
            self.assertEqual(2, manifest["source_line"])
            self.assertNotEqual(manifest["source_sha256"], manifest["mutant_sha256"])
            self.assertIn("MUTANT drop-remove-reverse-link", destination.read_text())

    def test_missing_anchor_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "list.c"
            source.write_text("void f(void) {}\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "occurs 0 times"):
                create_mutant(source, root / "mutant.c", "drop-remove-reverse-link")


if __name__ == "__main__":
    unittest.main()
