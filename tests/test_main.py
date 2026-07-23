import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import main


class ParserTests(unittest.TestCase):
    def test_readme_precedence_and_associativity(self) -> None:
        prop = main.parse_prop("~A*B+C->D->E")
        self.assertEqual(main.format_prop(prop), "~A*B+C->D->E")
        self.assertEqual(main.parse_prop(main.format_prop(prop)), prop)

    def test_sequent_context_is_a_set(self) -> None:
        actual = main.parse_sequent("B, A, A |- A, A")
        expected = main.parse_sequent("A, B |- A")
        self.assertEqual(actual, expected)
        self.assertEqual(main.format_sequent(actual), "A, B |- A")

    def test_empty_sides_are_parsed(self) -> None:
        self.assertEqual(main.format_sequent(main.parse_sequent("|- A")), "|- A")
        self.assertEqual(main.format_sequent(main.parse_sequent("A |-")), "A |-")

    def test_bad_separator_is_rejected(self) -> None:
        with self.assertRaises(main.ParseError):
            main.parse_sequent("A,,B |- A")

    def test_reserved_identifier_is_rejected(self) -> None:
        with self.assertRaises(main.ParseError):
            main.parse_sequent("Type |- Type")


class GeneratorTests(unittest.TestCase):
    def test_default_output_is_only_n3(self) -> None:
        generated = main.generate_n3()
        self.assertTrue(generated.startswith("Type A;\n"))
        self.assertNotIn("\nTrue\n", generated)
        self.assertIn("[|- A->A]", generated)
        self.assertTrue(generated.endswith("print proof1;\n"))

    def test_cli_emits_the_generated_program_once(self) -> None:
        result = subprocess.run(
            [sys.executable, str(ROOT / "main.py")],
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, main.generate_n3())
        self.assertEqual(result.stderr, "")

    def test_unprovable_sequent_is_rejected(self) -> None:
        with self.assertRaises(main.UnprovableError):
            main.generate_n3("A |- B")

    def test_proof_names_do_not_collide_with_prop_names(self) -> None:
        generated = main.generate_n3("proof0 |- proof0")
        self.assertIn("Type proof0;", generated)
        self.assertIn("proof1 = Id<proof0>()", generated)
        self.assertNotIn("proof0 = Id<proof0>()", generated)

    def test_generated_conclusion_exactly_matches_goal(self) -> None:
        regressions = (
            "A*B, A |- B",
            "A, A+B |- A+C",
            "B, A->B |- B+C",
            "~A, A*C |- A",
            "A*B, A*B |- A",
            "A |- A, A*B",
        )
        for text in regressions:
            with self.subTest(text=text):
                goal = main.parse_sequent(text)
                self.assertEqual(main.synthesize(goal).conclusion, goal)


@unittest.skipUnless(shutil.which("g++"), "g++ is required for integration tests")
class CppKernelIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.tempdir = tempfile.TemporaryDirectory()
        cls.kernel = Path(cls.tempdir.name) / "proofassistant-main"
        subprocess.run(
            [
                "g++",
                "-std=c++17",
                str(ROOT / "main.cpp"),
                "-o",
                str(cls.kernel),
            ],
            check=True,
            capture_output=True,
            text=True,
        )

    @classmethod
    def tearDownClass(cls) -> None:
        cls.tempdir.cleanup()

    def test_generated_proofs_are_accepted_by_cpp_kernel(self) -> None:
        cases = (
            main.DEFAULT_SEQUENT,
            "~(A*B) |- ~A + ~B",
            "A->B, B->C, ~C |- ~A",
            "((A->B)*(B->C)), ((C->D)*(~D)) |- ~A",
            "A*B, A |- B",
            "A, A+B |- A+C",
            "B, A->B |- B+C",
            "P0 |- P0",
        )
        proof_path = Path(self.tempdir.name) / "generated.n3"
        for text in cases:
            with self.subTest(text=text):
                proof_path.write_text(main.generate_n3(text), encoding="utf-8")
                result = subprocess.run(
                    [str(self.kernel), str(proof_path)],
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("Proved :", result.stdout)


if __name__ == "__main__":
    unittest.main()
