import tempfile
import unittest
from pathlib import Path

from analyse_list_trace import CORE_KILLERS, analyse, load_trace


class AnalyseListTraceTests(unittest.TestCase):
    def _trace(self) -> str:
        return "\n".join(
            [
                '{"step":"ordered.empty","count":0,"cursor":"END","ring":[]}',
                '{"step":"ordered.A","count":1,"cursor":"END","ring":[{"id":"A","key":3}]}',
                '{"step":"ordered.B","count":2,"cursor":"END","ring":[{"id":"A","key":3},{"id":"B","key":3}]}',
                '{"step":"fifo.insert","count":2,"cursor":"F2","ring":[{"id":"F1","key":9},{"id":"F2","key":1}]}',
                '{"step":"fifo.next.F1","count":2,"cursor":"F1","ring":[{"id":"F1","key":9},{"id":"F2","key":1}]}',
                '{"step":"fifo.next.F2","count":2,"cursor":"F2","ring":[{"id":"F1","key":9},{"id":"F2","key":1}]}',
                '{"step":"fifo.remove.F2","count":1,"cursor":"F1","ring":[{"id":"F1","key":9}]}',
            ]
        )

    def test_core_false_invariants_get_concrete_witnesses(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "trace.jsonl"
            path.write_text(self._trace(), encoding="utf-8")
            result = analyse(load_trace(path), "TEST")
        killed = {item["candidate"] for item in result["killed_invariants"]}
        self.assertEqual(CORE_KILLERS, killed)
        self.assertEqual(["F1", "F2"], result["fifo_cursor_sequence"])

    def test_invalid_cursor_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "trace.jsonl"
            path.write_text(
                '{"step":"bad","count":0,"cursor":"ghost","ring":[]}\n',
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "neither END nor a member"):
                load_trace(path)


if __name__ == "__main__":
    unittest.main()
