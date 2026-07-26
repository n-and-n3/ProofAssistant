#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
extension_root="${project_root}/vscode-extension"

mkdir -p "${extension_root}/bin" "${extension_root}/server"

g++ \
    -std=c++23 \
    -O2 \
    -Wall \
    -Wextra \
    -Werror \
    "${project_root}/main3.cpp" \
    -o "${extension_root}/bin/proofassistant"

cp \
    "${project_root}/lsp/server.py" \
    "${extension_root}/server/server.py"

chmod +x \
    "${extension_root}/bin/proofassistant" \
    "${extension_root}/server/server.py"

node --check "${extension_root}/extension.js"
python3 -m py_compile "${extension_root}/server/server.py"

echo "Built ProofAssistant analyzer and VS Code extension assets."
