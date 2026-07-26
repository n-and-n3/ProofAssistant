#!/usr/bin/env python3
"""Minimal stdio LSP server for ProofAssistant.

The server intentionally uses full-document synchronization.  Compiler
analysis is delegated to the C++ frontend through `--analyze-json`.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import sys
from typing import Any


DOCUMENTS: dict[str, str] = {}
ANALYSES: dict[str, dict[str, Any]] = {}

TOKEN_TYPES = ["keyword", "function", "variable", "operator"]
TOKEN_TYPE_INDEX = {name: index for index, name in enumerate(TOKEN_TYPES)}

INFERENCE_RULES = {
    "Id": (1, 0),
    "KL": (1, 1),
    "KR": (1, 1),
    "andL": (2, 1),
    "andR": (2, 2),
    "orL": (2, 2),
    "orR": (2, 1),
    "impL": (2, 2),
    "impR": (2, 1),
    "notL": (1, 1),
    "notR": (1, 1),
    "cut": (1, 2),
}


def send(payload: dict[str, Any]) -> None:
    body = json.dumps(
        payload, ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")
    sys.stdout.buffer.write(f"Content-Length: {len(body)}\r\n\r\n".encode())
    sys.stdout.buffer.write(body)
    sys.stdout.buffer.flush()


def response(request_id: Any, result: Any) -> None:
    send({"jsonrpc": "2.0", "id": request_id, "result": result})


def error_response(request_id: Any, code: int, message: str) -> None:
    send(
        {
            "jsonrpc": "2.0",
            "id": request_id,
            "error": {"code": code, "message": message},
        }
    )


def notify(method: str, params: Any) -> None:
    send({"jsonrpc": "2.0", "method": method, "params": params})


def read_message() -> dict[str, Any] | None:
    headers: dict[str, str] = {}
    while True:
        line = sys.stdin.buffer.readline()
        if not line:
            return None
        if line in (b"\r\n", b"\n"):
            break
        name, value = line.decode("ascii").split(":", 1)
        headers[name.lower()] = value.strip()

    length = int(headers.get("content-length", "0"))
    if length <= 0:
        return None
    return json.loads(sys.stdin.buffer.read(length).decode("utf-8"))


def analyzer_path() -> Path:
    configured = os.environ.get("PROOFASSISTANT_ANALYZER")
    if configured:
        return Path(configured)

    root = Path(__file__).resolve().parent.parent
    candidates = [
        root / "bin" / "proofassistant",
        root / "main3",
    ]
    for candidate in candidates:
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return candidate
    raise FileNotFoundError(
        "ProofAssistant analyzer was not found. Run scripts/build_lsp.sh."
    )


def utf16_length(text: str) -> int:
    return len(text.encode("utf-16-le")) // 2


def byte_column_to_utf16(line: str, byte_column: int) -> int:
    prefix = line.encode("utf-8")[:byte_column]
    decoded = prefix.decode("utf-8", errors="ignore")
    return utf16_length(decoded)


def normalize_position(source: str, position: dict[str, int]) -> None:
    lines = source.splitlines()
    line_number = position["line"]
    if 0 <= line_number < len(lines):
        position["character"] = byte_column_to_utf16(
            lines[line_number], position["character"]
        )


def normalize_ranges(source: str, analysis: dict[str, Any]) -> None:
    for diagnostic in analysis.get("diagnostics", []):
        range_value = diagnostic.get("range")
        if range_value:
            normalize_position(source, range_value["start"])
            normalize_position(source, range_value["end"])
    for token in analysis.get("tokens", []):
        normalize_position(source, token["range"]["start"])
        normalize_position(source, token["range"]["end"])


def analyze(source: str) -> dict[str, Any]:
    process = subprocess.run(
        [str(analyzer_path()), "--analyze-json"],
        input=source,
        text=True,
        capture_output=True,
        timeout=15,
        check=False,
    )
    if process.returncode != 0:
        raise RuntimeError(
            process.stderr.strip()
            or f"Analyzer exited with status {process.returncode}."
        )
    result = json.loads(process.stdout)
    normalize_ranges(source, result)
    return result


def publish(uri: str) -> None:
    source = DOCUMENTS[uri]
    try:
        analysis = analyze(source)
        ANALYSES[uri] = analysis
        diagnostics = []
        for item in analysis.get("diagnostics", []):
            diagnostic: dict[str, Any] = {
                "range": item.get("range")
                or {
                    "start": {"line": 0, "character": 0},
                    "end": {"line": 0, "character": 0},
                },
                "severity": item.get("severity", 1),
                "code": item.get("code", "proofassistant-error"),
                "source": "ProofAssistant",
                "message": item.get("message", "Unknown error."),
            }
            diagnostics.append(diagnostic)
        notify(
            "textDocument/publishDiagnostics",
            {"uri": uri, "diagnostics": diagnostics},
        )
    except Exception as exception:
        ANALYSES.pop(uri, None)
        notify(
            "window/logMessage",
            {"type": 1, "message": f"ProofAssistant: {exception}"},
        )
        notify(
            "textDocument/publishDiagnostics",
            {
                "uri": uri,
                "diagnostics": [
                    {
                        "range": {
                            "start": {"line": 0, "character": 0},
                            "end": {"line": 0, "character": 0},
                        },
                        "severity": 1,
                        "code": "lsp-analyzer-error",
                        "source": "ProofAssistant",
                        "message": str(exception),
                    }
                ],
            },
        )


def position_in_range(
    position: dict[str, int], range_value: dict[str, Any]
) -> bool:
    point = (position["line"], position["character"])
    start = (
        range_value["start"]["line"],
        range_value["start"]["character"],
    )
    end = (
        range_value["end"]["line"],
        range_value["end"]["character"],
    )
    return start <= point < end


def token_at(uri: str, position: dict[str, int]) -> dict[str, Any] | None:
    analysis = ANALYSES.get(uri, {})
    for token in analysis.get("tokens", []):
        if position_in_range(position, token["range"]):
            return token
    return None


def hover(uri: str, position: dict[str, int]) -> dict[str, Any] | None:
    token = token_at(uri, position)
    if token is None:
        return None

    category_labels = {
        "identifier": "Identifier",
        "keyword": "Keyword",
        "syntaxSymbol": "Syntax symbol",
        "operator": "Logical operator",
        "function": "Inference rule",
    }
    lines = [
        f"```n3\n{token['text']}\n```",
        category_labels.get(token["category"], token["category"]),
    ]
    for diagnostic in ANALYSES.get(uri, {}).get("diagnostics", []):
        range_value = diagnostic.get("range")
        if range_value and position_in_range(position, range_value):
            lines.append(f"**{diagnostic.get('code', 'error')}**: "
                         f"{diagnostic['message']}")
    return {
        "contents": {"kind": "markdown", "value": "\n\n".join(lines)},
        "range": token["range"],
    }


def document_highlights(
    uri: str, position: dict[str, int]
) -> list[dict[str, Any]]:
    selected = token_at(uri, position)
    if selected is None:
        return []

    bracket_pairs = {"(": ")", "[": "]", "{": "}", "<": ">"}
    reverse_pairs = {closing: opening for opening, closing in bracket_pairs.items()}
    selected_text = selected["text"]
    if selected_text in bracket_pairs or selected_text in reverse_pairs:
        tokens = ANALYSES.get(uri, {}).get("tokens", [])
        try:
            selected_index = tokens.index(selected)
        except ValueError:
            return []

        if selected_text in bracket_pairs:
            opening = selected_text
            closing = bracket_pairs[opening]
            depth = 0
            indexes = range(selected_index, len(tokens))
        else:
            closing = selected_text
            opening = reverse_pairs[closing]
            depth = 0
            indexes = range(selected_index, -1, -1)

        for index in indexes:
            text = tokens[index]["text"]
            if selected_text in bracket_pairs:
                if text == opening:
                    depth += 1
                elif text == closing:
                    depth -= 1
            else:
                if text == closing:
                    depth += 1
                elif text == opening:
                    depth -= 1
            if depth == 0:
                return [
                    {"range": selected["range"], "kind": 1},
                    {"range": tokens[index]["range"], "kind": 1},
                ]
        return [{"range": selected["range"], "kind": 1}]

    if selected["category"] != "identifier":
        return []
    return [
        {"range": token["range"], "kind": 1}
        for token in ANALYSES.get(uri, {}).get("tokens", [])
        if token["category"] == "identifier"
        and token["text"] == selected["text"]
    ]


def semantic_tokens(uri: str) -> dict[str, list[int]]:
    encoded: list[int] = []
    previous_line = 0
    previous_character = 0
    tokens = sorted(
        ANALYSES.get(uri, {}).get("tokens", []),
        key=lambda item: (
            item["range"]["start"]["line"],
            item["range"]["start"]["character"],
        ),
    )
    for token in tokens:
        category = token["category"]
        token_type = {
            "keyword": "keyword",
            "function": "function",
            "identifier": "variable",
            "operator": "operator",
        }.get(category)
        if (
            category == "syntaxSymbol" and
            token["text"] in {"|-", "="}
        ):
            token_type = "operator"
        if token_type is None:
            continue
        start = token["range"]["start"]
        end = token["range"]["end"]
        if start["line"] != end["line"]:
            continue
        line = start["line"]
        character = start["character"]
        length = max(1, end["character"] - character)
        delta_line = line - previous_line
        delta_character = (
            character - previous_character if delta_line == 0 else character
        )
        encoded.extend(
            [
                delta_line,
                delta_character,
                length,
                TOKEN_TYPE_INDEX[token_type],
                0,
            ]
        )
        previous_line = line
        previous_character = character
    return {"data": encoded}


def inference_rule_completion(name: str) -> dict[str, Any]:
    template_arity, premise_arity = INFERENCE_RULES[name]
    return {
        "label": name,
        "kind": 3,
        "detail": (
            f"Inference rule: {template_arity} proposition argument(s), "
            f"{premise_arity} premise(s)"
        ),
        "insertText": name,
        "insertTextFormat": 1,
        "sortText": "1-" + name,
    }


def completion_items(
    uri: str, position: dict[str, int]
) -> list[dict[str, Any]]:
    source = DOCUMENTS.get(uri, "")
    lines = source.splitlines()
    line_number = position["line"]
    line = lines[line_number] if 0 <= line_number < len(lines) else ""

    # Convert the LSP UTF-16 column into a Python character index.
    target_units = position["character"]
    used_units = 0
    character_index = 0
    for character in line:
        width = utf16_length(character)
        if used_units + width > target_units:
            break
        used_units += width
        character_index += 1
    prefix = line[:character_index]

    if re.search(r"\bprint\s+[A-Za-z0-9_]*$", prefix):
        return []

    tokens_before = []
    for token in ANALYSES.get(uri, {}).get("tokens", []):
        start = token["range"]["start"]
        if (start["line"], start["character"]) < (
            position["line"], position["character"]
        ):
            tokens_before.append(token)
    angle_depth = 0
    for token in tokens_before:
        if token["text"] == "<":
            angle_depth += 1
        elif token["text"] == ">" and angle_depth > 0:
            angle_depth -= 1
    if angle_depth > 0:
        return []

    statement_items = [
        {
            "label": "Type",
            "kind": 14,
            "detail": "Declare a proposition variable",
            "insertText": "Type",
            "insertTextFormat": 1,
            "sortText": "0-Type",
        },
        {
            "label": "auto",
            "kind": 14,
            "detail": "Infer and bind a proof",
            "insertText": "auto",
            "insertTextFormat": 1,
            "sortText": "0-auto",
        },
        {
            "label": "print",
            "kind": 14,
            "detail": "Print a proved sequent",
            "insertText": "print",
            "insertTextFormat": 1,
            "sortText": "0-print",
        }
    ]
    rule_items = [
        inference_rule_completion(name) for name in INFERENCE_RULES
    ]

    if not prefix.strip():
        return statement_items
    return rule_items + statement_items


def handle(message: dict[str, Any]) -> bool:
    method = message.get("method")
    params = message.get("params", {})
    request_id = message.get("id")

    if method == "initialize":
        response(
            request_id,
            {
                "capabilities": {
                    "textDocumentSync": {
                        "openClose": True,
                        "change": 1,
                        "save": {"includeText": True},
                    },
                    "hoverProvider": True,
                    "completionProvider": {
                        "triggerCharacters": ["<", "(", ",", " "],
                        "resolveProvider": False,
                    },
                    "documentHighlightProvider": True,
                    "semanticTokensProvider": {
                        "legend": {
                            "tokenTypes": TOKEN_TYPES,
                            "tokenModifiers": [],
                        },
                        "full": True,
                    },
                },
                "serverInfo": {
                    "name": "ProofAssistant Language Server",
                    "version": "0.1.0",
                },
            },
        )
    elif method == "initialized":
        pass
    elif method == "shutdown":
        response(request_id, None)
    elif method == "exit":
        return False
    elif method == "textDocument/didOpen":
        document = params["textDocument"]
        DOCUMENTS[document["uri"]] = document["text"]
        publish(document["uri"])
    elif method == "textDocument/didChange":
        uri = params["textDocument"]["uri"]
        changes = params.get("contentChanges", [])
        if changes:
            # Full synchronization: the last change contains the whole text.
            DOCUMENTS[uri] = changes[-1]["text"]
            publish(uri)
    elif method == "textDocument/didSave":
        uri = params["textDocument"]["uri"]
        if "text" in params:
            DOCUMENTS[uri] = params["text"]
        if uri in DOCUMENTS:
            publish(uri)
    elif method == "textDocument/didClose":
        uri = params["textDocument"]["uri"]
        DOCUMENTS.pop(uri, None)
        ANALYSES.pop(uri, None)
        notify(
            "textDocument/publishDiagnostics",
            {"uri": uri, "diagnostics": []},
        )
    elif method == "textDocument/hover":
        uri = params["textDocument"]["uri"]
        response(request_id, hover(uri, params["position"]))
    elif method == "textDocument/completion":
        uri = params["textDocument"]["uri"]
        response(
            request_id,
            {
                "isIncomplete": False,
                "items": completion_items(uri, params["position"]),
            },
        )
    elif method == "textDocument/documentHighlight":
        uri = params["textDocument"]["uri"]
        response(
            request_id,
            document_highlights(uri, params["position"]),
        )
    elif method == "textDocument/semanticTokens/full":
        uri = params["textDocument"]["uri"]
        response(request_id, semantic_tokens(uri))
    elif request_id is not None:
        error_response(request_id, -32601, f"Method not found: {method}")
    return True


def main() -> int:
    while True:
        message = read_message()
        if message is None:
            return 0
        try:
            if not handle(message):
                return 0
        except Exception as exception:
            if "id" in message:
                error_response(message["id"], -32603, str(exception))
            else:
                notify(
                    "window/logMessage",
                    {"type": 1, "message": f"ProofAssistant: {exception}"},
                )


if __name__ == "__main__":
    raise SystemExit(main())
