import tempfile
import unittest
from pathlib import Path

import source_scope


class SourceScopeTests(unittest.TestCase):
    def test_directive_macro_braces_do_not_hide_functions(self) -> None:
        source = """\
#define WRAP(x) do { x; } while (0)
/* comment with { } */
static int helper(int x) { return x + 1; }
int root(int x)
{
  WRAP(x = helper(x));
  return x;
}
"""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "sample.c"
            path.write_text(source, encoding="latin-1")
            macros = source_scope._macro_inventory(path, source)
            functions = source_scope.parse_file(path, {macro.name for macro in macros})

        by_name = {function.name: function for function in functions}
        self.assertEqual(set(by_name), {"helper", "root"})
        self.assertEqual(by_name["root"].calls, ("helper",))
        self.assertEqual(by_name["root"].macros, ("WRAP",))
        closure, unresolved = source_scope.transitive_closure(by_name, ["root"])
        self.assertEqual(closure, ["helper", "root"])
        self.assertEqual(unresolved, [])

    def test_comment_and_literal_call_shapes_are_ignored(self) -> None:
        source = """\
void root(void) {
  /* fake_call(); */
  const char *text = "also_fake()";
  real_call();
}
"""
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "sample.c"
            path.write_text(source, encoding="latin-1")
            function = source_scope.parse_file(path, set())[0]

        self.assertEqual(function.calls, ("real_call",))


if __name__ == "__main__":
    unittest.main()
