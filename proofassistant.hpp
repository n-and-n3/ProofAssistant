#pragma once

#include <cstdint>
#include <iosfwd>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

namespace proofassistant {

// LSP positions are zero-based. `character` is kept separate from the
// compiler's current one-based source columns so the conversion boundary is
// explicit and can later be upgraded to UTF-16 code units.
struct Position {
    std::uint32_t line = 0;
    std::uint32_t character = 0;
};

struct Range {
    Position start;
    Position end; // Exclusive, as required by LSP.
};

enum class DiagnosticSeverity {
    Error = 1,
    Warning = 2,
    Information = 3,
    Hint = 4,
};

enum class DiagnosticPhase {
    Parse,
    Semantic,
    Internal,
};

struct Diagnostic {
    DiagnosticSeverity severity = DiagnosticSeverity::Error;
    DiagnosticPhase phase = DiagnosticPhase::Internal;
    std::string code;
    std::string message;
    std::optional<Range> range;
};

enum class TokenCategory {
    Identifier,
    Keyword,
    SyntaxSymbol,
    LogicalConnective,
    InferenceRule,
};

struct TokenInfo {
    std::string text;
    TokenCategory category = TokenCategory::Identifier;
    Range range;
};

// This is the stable boundary intended for both the CLI and a future language
// server. LSP code should consume this result instead of reading stderr or
// catching compiler exceptions.
struct AnalysisResult {
    bool success = false;
    std::vector<Diagnostic> diagnostics;
    std::vector<TokenInfo> tokens;
};

struct ExecutionOptions {
    bool generate_latex = false;
};

struct ExecutionResult {
    bool success = false;
    std::vector<Diagnostic> diagnostics;
    std::string print_output;
    std::string latex;
};

// Kept as a compatibility view for callers that only request LaTeX.
struct LatexResult {
    bool success = false;
    std::vector<Diagnostic> diagnostics;
    std::string latex;
};

AnalysisResult analyze(std::string_view source);
ExecutionResult execute(
    std::string_view source,
    ExecutionOptions options = {}
);
LatexResult render_latex(std::string_view source);

// Thin CLI helper. Keeping file I/O out of `analyze` lets an LSP analyze the
// editor's in-memory document without saving it first.
int run_file(
    std::string_view path,
    std::ostream& standard_output,
    std::ostream& standard_error
);

int run_latex_file(
    std::string_view path,
    std::ostream& standard_output,
    std::ostream& standard_error
);

} // namespace proofassistant

// Define this in exactly one translation unit to build the implementation
// without separately listing proofassistant.cpp on the compiler command line.
#ifdef PROOFASSISTANT_IMPLEMENTATION
#include "proofassistant.cpp"
#endif
