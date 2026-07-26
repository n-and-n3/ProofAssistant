#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
"${project_root}/scripts/build_lsp.sh"

if [[ -n "${VSCODE_EXTENSIONS_DIR:-}" ]]; then
    extensions_root="${VSCODE_EXTENSIONS_DIR}"
elif [[ -d "${HOME}/.vscode-server/extensions" ]]; then
    extensions_root="${HOME}/.vscode-server/extensions"
else
    extensions_root="${HOME}/.vscode/extensions"
fi

extension_target="${extensions_root}/local.proofassistant-language-support-0.1.0"
mkdir -p "${extension_target}"

cp \
    "${project_root}/vscode-extension/package.json" \
    "${project_root}/vscode-extension/language-configuration.json" \
    "${project_root}/vscode-extension/extension.js" \
    "${extension_target}/"

mkdir -p "${extension_target}/bin" "${extension_target}/server"
cp \
    "${project_root}/vscode-extension/bin/proofassistant" \
    "${extension_target}/bin/proofassistant"
cp \
    "${project_root}/vscode-extension/server/server.py" \
    "${extension_target}/server/server.py"
chmod +x \
    "${extension_target}/bin/proofassistant" \
    "${extension_target}/server/server.py"

echo "Installed extension to ${extension_target}"
echo "Reload the VS Code window to activate ProofAssistant support."
