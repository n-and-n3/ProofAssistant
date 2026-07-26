#include "proofassistant.hpp"

#include <fstream>
#include <sstream>

// main2.cpp is currently the legacy implementation unit. Defining this macro
// removes only its CLI entry point; the public API above remains independent.
// The next refactoring step can move tokenizer/parser/evaluator definitions
// into normal implementation files without changing proofassistant.hpp.
#define PROOFASSISTANT_LIBRARY_MODE
#include "main2.cpp"
#undef PROOFASSISTANT_LIBRARY_MODE

namespace proofassistant {
namespace {

Range to_public_range(const SourceSpan& span) {
    return Range{
        Position{
            static_cast<std::uint32_t>(span.start_line - 1),
            static_cast<std::uint32_t>(span.start_column - 1)
        },
        Position{
            static_cast<std::uint32_t>(span.end_line - 1),
            static_cast<std::uint32_t>(span.end_column)
        }
    };
}

TokenCategory to_public_token_category(::TokenKind kind) {
    if (kind == ::TokenKind::Identifier) {
        return TokenCategory::Identifier;
    } else if (kind == ::TokenKind::Keyword) {
        return TokenCategory::Keyword;
    } else if (kind == ::TokenKind::SyntaxSymbol) {
        return TokenCategory::SyntaxSymbol;
    } else if (kind == ::TokenKind::LogicalConnective) {
        return TokenCategory::LogicalConnective;
    } else if (kind == ::TokenKind::InferenceRule) {
        return TokenCategory::InferenceRule;
    } else {
        throw std::runtime_error("Unknown internal token kind.");
    }
}

Diagnostic make_diagnostic(const InternalDiagnostic& internal) {
    Diagnostic diagnostic;
    diagnostic.message = internal.message;
    diagnostic.code = internal.code;
    if (internal.source_span) {
        diagnostic.range = to_public_range(*internal.source_span);
    }

    if (internal.phase == InternalDiagnosticPhase::Parser) {
        diagnostic.phase = DiagnosticPhase::Parse;
    } else if (internal.phase == InternalDiagnosticPhase::Semantic) {
        diagnostic.phase = DiagnosticPhase::Semantic;
    } else if (internal.phase == InternalDiagnosticPhase::Lexer) {
        diagnostic.phase = DiagnosticPhase::Parse;
    } else {
        throw std::runtime_error("Unknown internal diagnostic phase.");
    }

    if (internal.severity == InternalDiagnosticSeverity::Error) {
        diagnostic.severity = DiagnosticSeverity::Error;
    } else if (internal.severity == InternalDiagnosticSeverity::Warning) {
        diagnostic.severity = DiagnosticSeverity::Warning;
    } else if (
        internal.severity == InternalDiagnosticSeverity::Information
    ) {
        diagnostic.severity = DiagnosticSeverity::Information;
    } else if (internal.severity == InternalDiagnosticSeverity::Hint) {
        diagnostic.severity = DiagnosticSeverity::Hint;
    } else {
        throw std::runtime_error("Unknown internal diagnostic severity.");
    }
    return diagnostic;
}

Diagnostic make_internal_diagnostic(const std::exception& error) {
    return Diagnostic{
        DiagnosticSeverity::Error,
        DiagnosticPhase::Internal,
        "internal-error",
        error.what(),
        std::nullopt
    };
}

struct ProofTree {
    std::string rule;
    ::Sequent conclusion;
    std::vector<std::shared_ptr<ProofTree>> premises;
};

using ProofEnvironment =
    std::unordered_map<std::string, std::shared_ptr<ProofTree>>;

std::shared_ptr<ProofTree> build_proof_tree(
    const std::shared_ptr<ASTNode>& node,
    const ::SymbolTable& context,
    const ProofEnvironment& proofs,
    DiagnosticSink& diagnostics
) {
    if (!node) {
        throw std::logic_error(
            "Internal error: expected a proof node, but found null."
        );
    } else if (node->kind == "sequent_identifier") {
        require_child_count(node, 0);
        auto proof = proofs.find(node->content);
        if (proof == proofs.end()) {
            throw_validation_error(
                *node,
                "Sequent variable '" + node->content +
                    "' has no recorded proof tree."
            );
        } else {
            return proof->second;
        }
    } else if (node->kind == "inference_rules") {
        require_child_count(node, 2);
        const auto& premise_list = node->children[1];
        require_node_kind(premise_list, "prop_args");

        std::vector<std::shared_ptr<ProofTree>> premises;
        premises.reserve(premise_list->children.size());
        for (const auto& premise : premise_list->children) {
            premises.push_back(
                build_proof_tree(premise, context, proofs, diagnostics)
            );
        }

        return std::make_shared<ProofTree>(ProofTree{
            node->content,
            evaluate_proof(node, context, diagnostics),
            std::move(premises)
        });
    } else {
        throw std::logic_error(
            "Internal error: expected proof AST kind 'sequent_identifier' "
            "or 'inference_rules', but found '" + node->kind + "'."
        );
    }
}

std::string latex_escape(std::string_view text) {
    std::string result;
    for (char character : text) {
        if (character == '\\') {
            result += R"(\textbackslash{})";
        } else if (character == '{') {
            result += R"(\{)";
        } else if (character == '}') {
            result += R"(\})";
        } else if (character == '#') {
            result += R"(\#)";
        } else if (character == '$') {
            result += R"(\$)";
        } else if (character == '%') {
            result += R"(\%)";
        } else if (character == '&') {
            result += R"(\&)";
        } else if (character == '_') {
            result += R"(\_)";
        } else if (character == '^') {
            result += R"(\textasciicircum{})";
        } else if (character == '~') {
            result += R"(\textasciitilde{})";
        } else {
            result += character;
        }
    }
    return result;
}

std::string prop_to_latex(const std::shared_ptr<const ASTNode>& node) {
    if (!node) {
        throw std::logic_error(
            "Internal error: proposition AST root is null."
        );
    } else if (node->kind == "prop_identifier") {
        if (!node->children.empty()) {
            throw std::logic_error(
                "Internal error: a proposition identifier has child nodes."
            );
        } else {
            return R"(\mathit{)" + latex_escape(node->content) + "}";
        }
    } else if (node->kind == "logical") {
        if (node->content == "not") {
            require_child_count(
                std::const_pointer_cast<ASTNode>(node),
                1
            );
            return R"(\neg )" + prop_to_latex(node->children[0]);
        } else if (
            node->content == "and" ||
            node->content == "or" ||
            node->content == "imp"
        ) {
            require_child_count(
                std::const_pointer_cast<ASTNode>(node),
                2
            );
            std::string operation;
            if (node->content == "and") {
                operation = R"(\land)";
            } else if (node->content == "or") {
                operation = R"(\lor)";
            } else if (node->content == "imp") {
                operation = R"(\to)";
            } else {
                throw std::logic_error(
                    "Internal error: unknown binary logical operation '" +
                        node->content + "'."
                );
            }
            return R"(\left()" + prop_to_latex(node->children[0]) +
                " " + operation + " " +
                prop_to_latex(node->children[1]) + R"(\right))";
        } else {
            throw std::logic_error(
                "Internal error: unknown logical operation '" +
                    node->content + "'."
            );
        }
    } else {
        throw std::logic_error(
            "Internal error: cannot render AST kind '" + node->kind +
                "' as a proposition."
        );
    }
}

std::string sequent_to_latex(const ::Sequent& sequent) {
    std::vector<std::string> antecedent;
    std::vector<std::string> succedent;
    antecedent.reserve(sequent.antecedent.size());
    succedent.reserve(sequent.succedent.size());

    for (const auto& prop : sequent.antecedent) {
        antecedent.push_back(prop_to_latex(prop.root));
    }
    for (const auto& prop : sequent.succedent) {
        succedent.push_back(prop_to_latex(prop.root));
    }
    std::sort(antecedent.begin(), antecedent.end());
    std::sort(succedent.begin(), succedent.end());

    auto join = [](const std::vector<std::string>& values) {
        std::string result;
        for (std::size_t index = 0; index < values.size(); ++index) {
            if (index != 0) {
                result += ", ";
            }
            result += values[index];
        }
        return result;
    };

    return join(antecedent) + R"( \vdash )" + join(succedent);
}

void append_proof_tree_latex(
    const std::shared_ptr<ProofTree>& proof,
    std::string& output
) {
    if (!proof) {
        throw std::runtime_error(
            "Validation error at unknown location: proof tree node is null."
        );
    } else if (proof->premises.size() > 2) {
        throw std::runtime_error(
            "Validation error at unknown location: bussproofs output supports "
            "at most two premises per rule in this language."
        );
    }

    for (const auto& premise : proof->premises) {
        append_proof_tree_latex(premise, output);
    }

    const std::string conclusion =
        "{$" + sequent_to_latex(proof->conclusion) + "$}\n";

    if (proof->premises.empty()) {
        output += "\\AxiomC{}\n";
        output += R"(\RightLabel{\scriptsize $\mathrm{)" +
            latex_escape(proof->rule) + "}$}\n";
        output += R"(\UnaryInfC)" + conclusion;
    } else if (proof->premises.size() == 1) {
        output += R"(\RightLabel{\scriptsize $\mathrm{)" +
            latex_escape(proof->rule) + "}$}\n";
        output += R"(\UnaryInfC)" + conclusion;
    } else if (proof->premises.size() == 2) {
        output += R"(\RightLabel{\scriptsize $\mathrm{)" +
            latex_escape(proof->rule) + "}$}\n";
        output += R"(\BinaryInfC)" + conclusion;
    } else {
        throw std::runtime_error(
            "Validation error at unknown location: unsupported premise count."
        );
    }
}

std::string make_latex_document(
    const std::vector<std::pair<std::string, std::shared_ptr<ProofTree>>>&
        printed_proofs
) {
    std::string output =
        "\\documentclass{article}\n"
        "\\usepackage{amsmath}\n"
        "\\usepackage{bussproofs}\n"
        "\\usepackage{adjustbox}\n"
        "\\usepackage[a4paper,landscape,margin=1cm]{geometry}\n"
        "\\newenvironment{bprooftree}\n"
        "  {\\leavevmode\\hbox\\bgroup}\n"
        "  {\\DisplayProof\\egroup}\n"
        "\\begin{document}\n";

    if (printed_proofs.empty()) {
        output +=
            "\\noindent No proof was selected. Add a "
            "\\texttt{print} statement to the source program.\n";
    } else {
        for (std::size_t index = 0; index < printed_proofs.size(); ++index) {
            const auto& [name, proof] = printed_proofs[index];
            if (index != 0) {
                output += "\\clearpage\n";
            }
            output += "\\section*{Proof of \\texttt{" +
                latex_escape(name) + "}}\n"
                "\\begin{center}\n"
                "\\begin{adjustbox}{max width=\\textwidth}\n"
                "\\begin{bprooftree}\n";
            append_proof_tree_latex(proof, output);
            output +=
                "\\end{bprooftree}\n"
                "\\end{adjustbox}\n"
                "\\end{center}\n";
        }
    }
    output += "\\end{document}\n";
    return output;
}

} // namespace

AnalysisResult analyze(std::string_view source) {
    AnalysisResult result;
    try {
        const auto internal_tokens = ::tokenize(std::string(source));
        result.tokens.reserve(internal_tokens.size());
        for (const auto& token : internal_tokens) {
            result.tokens.push_back(TokenInfo{
                token.text,
                to_public_token_category(token.kind),
                to_public_range(token.source_span)
            });
        }
        DiagnosticSink diagnostics;
        const auto root = ::parser(internal_tokens, diagnostics);
        ::SymbolTable context;
        ::evaluate(root, context, diagnostics);
        for (const auto& diagnostic : diagnostics.diagnostics()) {
            result.diagnostics.push_back(make_diagnostic(diagnostic));
        }
        result.success = !diagnostics.has_errors();
        return result;
    } catch (const std::exception& error) {
        result.success = false;
        result.diagnostics.push_back(make_internal_diagnostic(error));
        return result;
    } catch (...) {
        result.success = false;
        result.diagnostics.push_back(Diagnostic{
            DiagnosticSeverity::Error,
            DiagnosticPhase::Internal,
            "unknown-exception",
            "An unknown non-standard exception occurred.",
            std::nullopt
        });
        return result;
    }
}

ExecutionResult execute(
    std::string_view source,
    ExecutionOptions options
) {
    ExecutionResult result;
    try {
        const auto tokens = ::tokenize(std::string(source));
        DiagnosticSink diagnostics;
        const auto root = ::parser(tokens, diagnostics);
        require_node_kind(root, "code");

        ::SymbolTable context;
        ProofEnvironment proofs;
        std::vector<std::pair<std::string, std::shared_ptr<ProofTree>>>
            printed_proofs;

        for (const auto& statement : root->children) {
            const std::size_t diagnostic_count_before =
                diagnostics.size();
            require_node_kind(statement, "prefix");
            if (statement->content == "Type") {
                evaluate_statement(statement, context, diagnostics);
            } else if (statement->content == "auto") {
                require_child_count(statement, 2);
                const auto& identifier = statement->children[0];
                require_node_kind(identifier, "sequent_identifier");
                evaluate_statement(statement, context, diagnostics);
                if (
                    options.generate_latex &&
                    diagnostics.size() == diagnostic_count_before
                ) {
                    auto proof = build_proof_tree(
                        statement->children[1],
                        context,
                        proofs,
                        diagnostics
                    );
                    proofs.emplace(identifier->content, std::move(proof));
                }
            } else if (statement->content == "var") {
                require_child_count(statement, 3);
                const auto& identifier = statement->children[1];
                require_node_kind(identifier, "sequent_identifier");
                evaluate_statement(statement, context, diagnostics);
                if (
                    options.generate_latex &&
                    diagnostics.size() == diagnostic_count_before
                ) {
                    auto proof = build_proof_tree(
                        statement->children[2],
                        context,
                        proofs,
                        diagnostics
                    );
                    proofs.emplace(identifier->content, std::move(proof));
                }
            } else if (statement->content == "print") {
                require_child_count(statement, 1);
                const auto& identifier = statement->children[0];
                require_node_kind(identifier, "sequent_identifier");
                evaluate_statement(statement, context, diagnostics);
                if (diagnostics.size() == diagnostic_count_before) {
                    const Sequent* value =
                        context.find_sequent(identifier->content);
                    if (!value) {
                        throw std::logic_error(
                            "Internal error: validated print target is "
                            "missing from the symbol table."
                        );
                    }
                    result.print_output +=
                        "Proved : " + value->to_string() + "\n";

                    if (options.generate_latex) {
                        auto proof = proofs.find(identifier->content);
                        if (proof == proofs.end()) {
                            throw std::logic_error(
                                "Internal error: a validated sequent has "
                                "no recorded proof tree."
                            );
                        }
                        printed_proofs.emplace_back(
                            identifier->content,
                            proof->second
                        );
                    }
                }
            } else {
                throw std::logic_error(
                    "Internal error: unknown statement type '" +
                        statement->content + "'."
                );
            }
        }

        for (const auto& diagnostic : diagnostics.diagnostics()) {
            result.diagnostics.push_back(make_diagnostic(diagnostic));
        }
        result.success = !diagnostics.has_errors();
        if (options.generate_latex && result.success) {
            result.latex = make_latex_document(printed_proofs);
        }
        return result;
    } catch (const SemanticFailure& failure) {
        result.success = false;
        result.diagnostics.push_back(
            make_diagnostic(failure.diagnostic())
        );
        return result;
    } catch (const std::exception& error) {
        result.success = false;
        result.diagnostics.push_back(make_internal_diagnostic(error));
        return result;
    } catch (...) {
        result.success = false;
        result.diagnostics.push_back(Diagnostic{
            DiagnosticSeverity::Error,
            DiagnosticPhase::Internal,
            "unknown-exception",
            "An unknown non-standard exception occurred.",
            std::nullopt
        });
        return result;
    }
}

LatexResult render_latex(std::string_view source) {
    ExecutionResult execution = execute(
        source,
        ExecutionOptions{.generate_latex = true}
    );
    return LatexResult{
        .success = execution.success,
        .diagnostics = move(execution.diagnostics),
        .latex = move(execution.latex),
    };
}

int run_file(
    std::string_view path,
    std::ostream& standard_output,
    std::ostream& standard_error
) {
    std::ifstream input{std::string(path)};
    if (!input.is_open()) {
        standard_error << "Error: could not open input file '" << path << "'.\n";
        return 1;
    } else {
        std::ostringstream buffer;
        buffer << input.rdbuf();
        ExecutionResult result = execute(buffer.str());
        standard_output << result.print_output;

        if (result.success) {
            standard_output << "0\n";
            return 0;
        } else {
            for (const auto& diagnostic : result.diagnostics) {
                standard_error << diagnostic.message << "\n";
            }
            return 1;
        }
    }
}

int run_latex_file(
    std::string_view path,
    std::ostream& standard_output,
    std::ostream& standard_error
) {
    std::ifstream input{std::string(path)};
    if (!input.is_open()) {
        standard_error << "Error: could not open input file '" << path << "'.\n";
        return 1;
    } else {
        std::ostringstream buffer;
        buffer << input.rdbuf();
        LatexResult result = render_latex(buffer.str());
        if (result.success) {
            standard_output << result.latex;
            return 0;
        } else {
            for (const auto& diagnostic : result.diagnostics) {
                standard_error << diagnostic.message << "\n";
            }
            return 1;
        }
    }
}

} // namespace proofassistant
