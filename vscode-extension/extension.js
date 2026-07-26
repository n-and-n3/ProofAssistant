"use strict";

const vscode = require("vscode");
const cp = require("child_process");
const path = require("path");

class StdioLanguageClient {
    constructor(context, diagnostics) {
        this.context = context;
        this.diagnostics = diagnostics;
        this.nextId = 1;
        this.pending = new Map();
        this.buffer = Buffer.alloc(0);
        this.process = undefined;
    }

    start() {
        const server = path.join(
            this.context.extensionPath, "server", "server.py"
        );
        const analyzer = path.join(
            this.context.extensionPath, "bin", "proofassistant"
        );
        this.process = cp.spawn("python3", [server], {
            env: {
                ...process.env,
                PROOFASSISTANT_ANALYZER: analyzer
            },
            stdio: ["pipe", "pipe", "pipe"]
        });
        this.process.stdout.on("data", chunk => this.consume(chunk));
        this.process.stderr.on("data", chunk => {
            console.error(`ProofAssistant LSP: ${chunk}`);
        });
        this.process.on("exit", code => {
            if (code !== 0 && code !== null) {
                vscode.window.showErrorMessage(
                    `ProofAssistant language server exited with ${code}.`
                );
            }
            for (const {reject} of this.pending.values()) {
                reject(new Error("Language server stopped."));
            }
            this.pending.clear();
        });
        return this.request("initialize", {
            processId: process.pid,
            rootUri: vscode.workspace.workspaceFolders?.[0]?.uri.toString()
                ?? null,
            capabilities: {}
        }).then(() => this.notify("initialized", {}));
    }

    stop() {
        if (!this.process) {
            return;
        }
        return this.request("shutdown", null)
            .catch(() => undefined)
            .then(() => {
                this.notify("exit", null);
                this.process = undefined;
            });
    }

    write(message) {
        if (!this.process) {
            throw new Error("Language server is not running.");
        }
        const body = Buffer.from(JSON.stringify({
            jsonrpc: "2.0",
            ...message
        }), "utf8");
        this.process.stdin.write(
            `Content-Length: ${body.length}\r\n\r\n`
        );
        this.process.stdin.write(body);
    }

    notify(method, params) {
        this.write({method, params});
    }

    request(method, params) {
        const id = this.nextId++;
        return new Promise((resolve, reject) => {
            this.pending.set(id, {resolve, reject});
            this.write({id, method, params});
        });
    }

    consume(chunk) {
        this.buffer = Buffer.concat([this.buffer, chunk]);
        while (true) {
            const separator = this.buffer.indexOf("\r\n\r\n");
            if (separator < 0) {
                return;
            }
            const header = this.buffer.subarray(0, separator).toString();
            const match = /Content-Length:\s*(\d+)/i.exec(header);
            if (!match) {
                this.buffer = this.buffer.subarray(separator + 4);
                continue;
            }
            const length = Number(match[1]);
            const bodyStart = separator + 4;
            if (this.buffer.length < bodyStart + length) {
                return;
            }
            const body = this.buffer
                .subarray(bodyStart, bodyStart + length)
                .toString("utf8");
            this.buffer = this.buffer.subarray(bodyStart + length);
            this.dispatch(JSON.parse(body));
        }
    }

    dispatch(message) {
        if (message.id !== undefined) {
            const pending = this.pending.get(message.id);
            if (!pending) {
                return;
            }
            this.pending.delete(message.id);
            if (message.error) {
                pending.reject(new Error(message.error.message));
            } else {
                pending.resolve(message.result);
            }
            return;
        }
        if (message.method === "textDocument/publishDiagnostics") {
            const uri = vscode.Uri.parse(message.params.uri);
            const diagnostics = message.params.diagnostics.map(item => {
                const diagnostic = new vscode.Diagnostic(
                    toRange(item.range),
                    item.message,
                    Math.max(0, item.severity - 1)
                );
                diagnostic.code = item.code;
                diagnostic.source = item.source;
                return diagnostic;
            });
            this.diagnostics.set(uri, diagnostics);
        } else if (message.method === "window/logMessage") {
            console.log(message.params.message);
        }
    }
}

function toPosition(value) {
    return new vscode.Position(value.line, value.character);
}

function toRange(value) {
    return new vscode.Range(
        toPosition(value.start),
        toPosition(value.end)
    );
}

function documentParams(document) {
    return {
        uri: document.uri.toString(),
        languageId: "proofassistant",
        version: document.version,
        text: document.getText()
    };
}

let client;

async function activate(context) {
    const diagnostics = vscode.languages.createDiagnosticCollection(
        "ProofAssistant"
    );
    context.subscriptions.push(diagnostics);

    client = new StdioLanguageClient(context, diagnostics);
    await client.start();

    const selector = {language: "proofassistant", scheme: "file"};
    const openDocument = document => {
        if (document.languageId === "proofassistant") {
            client.notify("textDocument/didOpen", {
                textDocument: documentParams(document)
            });
        }
    };

    for (const document of vscode.workspace.textDocuments) {
        openDocument(document);
    }

    context.subscriptions.push(
        vscode.workspace.onDidOpenTextDocument(openDocument),
        vscode.workspace.onDidChangeTextDocument(event => {
            if (event.document.languageId !== "proofassistant") {
                return;
            }
            client.notify("textDocument/didChange", {
                textDocument: {
                    uri: event.document.uri.toString(),
                    version: event.document.version
                },
                contentChanges: [{text: event.document.getText()}]
            });
        }),
        vscode.workspace.onDidSaveTextDocument(document => {
            if (document.languageId === "proofassistant") {
                client.notify("textDocument/didSave", {
                    textDocument: {uri: document.uri.toString()},
                    text: document.getText()
                });
            }
        }),
        vscode.workspace.onDidCloseTextDocument(document => {
            if (document.languageId === "proofassistant") {
                client.notify("textDocument/didClose", {
                    textDocument: {uri: document.uri.toString()}
                });
            }
        }),
        vscode.languages.registerHoverProvider(selector, {
            async provideHover(document, position) {
                const value = await client.request("textDocument/hover", {
                    textDocument: {uri: document.uri.toString()},
                    position
                });
                if (!value) {
                    return undefined;
                }
                return new vscode.Hover(
                    new vscode.MarkdownString(value.contents.value),
                    toRange(value.range)
                );
            }
        }),
        vscode.languages.registerCompletionItemProvider(
            selector,
            {
                async provideCompletionItems(document, position, token, context) {
                    const value = await client.request(
                        "textDocument/completion",
                        {
                            textDocument: {
                                uri: document.uri.toString()
                            },
                            position,
                            context: {
                                triggerKind: context.triggerKind,
                                triggerCharacter: context.triggerCharacter
                            }
                        }
                    );
                    return value.items.map(item => {
                        const completion = new vscode.CompletionItem(
                            item.label,
                            Math.max(0, (item.kind ?? 1) - 1)
                        );
                        completion.detail = item.detail;
                        completion.sortText = item.sortText;
                        if (item.insertTextFormat === 2) {
                            completion.insertText = new vscode.SnippetString(
                                item.insertText
                            );
                        } else if (item.insertText) {
                            completion.insertText = item.insertText;
                        }
                        return completion;
                    });
                }
            },
            "<",
            "(",
            ",",
            " "
        ),
        vscode.languages.registerDocumentHighlightProvider(selector, {
            async provideDocumentHighlights(document, position) {
                const values = await client.request(
                    "textDocument/documentHighlight",
                    {
                        textDocument: {uri: document.uri.toString()},
                        position
                    }
                );
                return values.map(value => new vscode.DocumentHighlight(
                    toRange(value.range),
                    Math.max(0, value.kind - 1)
                ));
            }
        })
    );

    const legend = new vscode.SemanticTokensLegend(
        ["keyword", "function", "variable", "operator"],
        []
    );
    context.subscriptions.push(
        vscode.languages.registerDocumentSemanticTokensProvider(
            selector,
            {
                async provideDocumentSemanticTokens(document) {
                    const value = await client.request(
                        "textDocument/semanticTokens/full",
                        {
                            textDocument: {
                                uri: document.uri.toString()
                            }
                        }
                    );
                    return new vscode.SemanticTokens(
                        new Uint32Array(value.data)
                    );
                }
            },
            legend
        )
    );
}

function deactivate() {
    if (client) {
        return client.stop();
    }
    return undefined;
}

module.exports = {activate, deactivate};
