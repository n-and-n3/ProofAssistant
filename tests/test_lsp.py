import json
import os
from pathlib import Path
import subprocess
import unittest


ROOT = Path(__file__).resolve().parents[1]
SERVER = ROOT / "lsp" / "server.py"
ANALYZER = ROOT / "vscode-extension" / "bin" / "proofassistant"


def frame(payload):
    body = json.dumps(payload, separators=(",", ":")).encode()
    return b"Content-Length: %d\r\n\r\n" % len(body) + body


def read_message(stream):
    headers = {}
    while True:
        line = stream.readline()
        if line in (b"\r\n", b"\n"):
            break
        if not line:
            raise EOFError("Language server stopped.")
        name, value = line.decode("ascii").split(":", 1)
        headers[name.lower()] = value.strip()
    length = int(headers["content-length"])
    return json.loads(stream.read(length))


class LanguageServerTest(unittest.TestCase):
    def setUp(self):
        environment = os.environ.copy()
        environment["PROOFASSISTANT_ANALYZER"] = str(ANALYZER)
        self.server = subprocess.Popen(
            ["python3", str(SERVER)],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=environment,
        )

    def tearDown(self):
        if self.server.poll() is None:
            self.server.terminate()
            self.server.wait(timeout=5)
        self.server.stdin.close()
        self.server.stdout.close()
        self.server.stderr.close()

    def send(self, payload):
        self.server.stdin.write(frame(payload))
        self.server.stdin.flush()

    def receive(self):
        return read_message(self.server.stdout)

    def test_diagnostics_hover_highlights_and_semantic_tokens(self):
        self.send(
            {
                "jsonrpc": "2.0",
                "id": 1,
                "method": "initialize",
                "params": {"capabilities": {}},
            }
        )
        initialized = self.receive()
        capabilities = initialized["result"]["capabilities"]
        self.assertEqual(capabilities["textDocumentSync"]["change"], 1)
        self.assertTrue(capabilities["hoverProvider"])
        self.assertIn("completionProvider", capabilities)
        self.assertTrue(capabilities["documentHighlightProvider"])
        self.assertTrue(capabilities["semanticTokensProvider"]["full"])

        uri = "file:///tmp/lsp-test.n3"
        source = "Type A;\nType A;\n"
        self.send(
            {
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": uri,
                        "languageId": "proofassistant",
                        "version": 1,
                        "text": source,
                    }
                },
            }
        )
        diagnostics = self.receive()
        self.assertEqual(
            diagnostics["method"],
            "textDocument/publishDiagnostics",
        )
        self.assertEqual(
            diagnostics["params"]["diagnostics"][0]["code"],
            "duplicate-definition",
        )

        position = {"line": 1, "character": 5}
        self.send(
            {
                "jsonrpc": "2.0",
                "id": 2,
                "method": "textDocument/hover",
                "params": {
                    "textDocument": {"uri": uri},
                    "position": position,
                },
            }
        )
        hover = self.receive()["result"]
        self.assertIn("Identifier", hover["contents"]["value"])
        self.assertIn("duplicate-definition", hover["contents"]["value"])

        self.send(
            {
                "jsonrpc": "2.0",
                "id": 3,
                "method": "textDocument/documentHighlight",
                "params": {
                    "textDocument": {"uri": uri},
                    "position": position,
                },
            }
        )
        highlights = self.receive()["result"]
        self.assertEqual(len(highlights), 2)

        self.send(
            {
                "jsonrpc": "2.0",
                "id": 4,
                "method": "textDocument/semanticTokens/full",
                "params": {"textDocument": {"uri": uri}},
            }
        )
        semantic_tokens = self.receive()["result"]["data"]
        self.assertGreater(len(semantic_tokens), 0)
        self.assertEqual(len(semantic_tokens) % 5, 0)

        bracket_source = (
            "Type A;\n"
            "Type B;\n"
            "auto p = KL<A->B>(missing);\n"
        )
        self.send(
            {
                "jsonrpc": "2.0",
                "method": "textDocument/didChange",
                "params": {
                    "textDocument": {"uri": uri, "version": 2},
                    "contentChanges": [{"text": bracket_source}],
                },
            }
        )
        self.assertEqual(
            self.receive()["method"],
            "textDocument/publishDiagnostics",
        )

        self.send(
            {
                "jsonrpc": "2.0",
                "id": 5,
                "method": "textDocument/documentHighlight",
                "params": {
                    "textDocument": {"uri": uri},
                    "position": {"line": 2, "character": 11},
                },
            }
        )
        angle_highlights = self.receive()["result"]
        self.assertEqual(len(angle_highlights), 2)
        self.assertEqual(
            {
                item["range"]["start"]["character"]
                for item in angle_highlights
            },
            {11, 16},
        )

        self.send(
            {
                "jsonrpc": "2.0",
                "id": 6,
                "method": "textDocument/documentHighlight",
                "params": {
                    "textDocument": {"uri": uri},
                    "position": {"line": 2, "character": 17},
                },
            }
        )
        round_highlights = self.receive()["result"]
        self.assertEqual(len(round_highlights), 2)

        self.send(
            {
                "jsonrpc": "2.0",
                "id": 7,
                "method": "textDocument/completion",
                "params": {
                    "textDocument": {"uri": uri},
                    "position": {"line": 2, "character": 12},
                    "context": {"triggerKind": 1},
                },
            }
        )
        proposition_completions = self.receive()["result"]["items"]
        self.assertEqual(proposition_completions, [])

        self.send(
            {
                "jsonrpc": "2.0",
                "id": 8,
                "method": "textDocument/completion",
                "params": {
                    "textDocument": {"uri": uri},
                    "position": {"line": 2, "character": 9},
                    "context": {"triggerKind": 1},
                },
            }
        )
        proof_completions = self.receive()["result"]["items"]
        labels = {item["label"] for item in proof_completions}
        self.assertIn("impR", labels)
        self.assertIn("Id", labels)
        imp_r = next(
            item for item in proof_completions
            if item["label"] == "impR"
        )
        self.assertEqual(imp_r["insertText"], "impR")
        self.assertEqual(imp_r["insertTextFormat"], 1)
        self.assertNotIn("A", labels)
        self.assertNotIn("B", labels)


if __name__ == "__main__":
    unittest.main()
