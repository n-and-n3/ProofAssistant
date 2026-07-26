#define PROOFASSISTANT_IMPLEMENTATION
#include "proofassistant.hpp"

#include <fstream>
#include <iostream>
#include <optional>
#include <sstream>
#include <string>

namespace {

std::string json_escape(std::string_view value) {
    std::string result;
    result.reserve(value.size() + 2);
    for (const unsigned char character : value) {
        if (character == '"') {
            result += "\\\"";
        } else if (character == '\\') {
            result += "\\\\";
        } else if (character == '\b') {
            result += "\\b";
        } else if (character == '\f') {
            result += "\\f";
        } else if (character == '\n') {
            result += "\\n";
        } else if (character == '\r') {
            result += "\\r";
        } else if (character == '\t') {
            result += "\\t";
        } else if (character < 0x20) {
            constexpr char digits[] = "0123456789abcdef";
            result += "\\u00";
            result += digits[character >> 4];
            result += digits[character & 0x0f];
        } else {
            result += static_cast<char>(character);
        }
    }
    return result;
}

void write_position(
    std::ostream& output,
    const proofassistant::Position& position
) {
    output << "{\"line\":" << position.line
           << ",\"character\":" << position.character << "}";
}

void write_range(
    std::ostream& output,
    const proofassistant::Range& range
) {
    output << "{\"start\":";
    write_position(output, range.start);
    output << ",\"end\":";
    write_position(output, range.end);
    output << "}";
}

std::string_view token_category_name(
    proofassistant::TokenCategory category
) {
    using proofassistant::TokenCategory;
    if (category == TokenCategory::Identifier) {
        return "identifier";
    } else if (category == TokenCategory::Keyword) {
        return "keyword";
    } else if (category == TokenCategory::SyntaxSymbol) {
        return "syntaxSymbol";
    } else if (category == TokenCategory::LogicalConnective) {
        return "operator";
    } else if (category == TokenCategory::InferenceRule) {
        return "function";
    } else {
        throw std::logic_error("Unknown public token category.");
    }
}

std::string_view diagnostic_phase_name(
    proofassistant::DiagnosticPhase phase
) {
    using proofassistant::DiagnosticPhase;
    if (phase == DiagnosticPhase::Parse) {
        return "parse";
    } else if (phase == DiagnosticPhase::Semantic) {
        return "semantic";
    } else if (phase == DiagnosticPhase::Internal) {
        return "internal";
    } else {
        throw std::logic_error("Unknown public diagnostic phase.");
    }
}

void write_analysis_json(
    std::ostream& output,
    const proofassistant::AnalysisResult& analysis
) {
    output << "{\"success\":"
           << (analysis.success ? "true" : "false")
           << ",\"diagnostics\":[";
    for (std::size_t index = 0;
         index < analysis.diagnostics.size();
         ++index) {
        if (index != 0) {
            output << ",";
        }
        const auto& diagnostic = analysis.diagnostics[index];
        output << "{\"severity\":"
               << static_cast<int>(diagnostic.severity)
               << ",\"phase\":\""
               << diagnostic_phase_name(diagnostic.phase)
               << "\",\"code\":\"" << json_escape(diagnostic.code)
               << "\",\"message\":\"" << json_escape(diagnostic.message)
               << "\",\"range\":";
        if (diagnostic.range) {
            write_range(output, *diagnostic.range);
        } else {
            output << "null";
        }
        output << "}";
    }
    output << "],\"tokens\":[";
    for (std::size_t index = 0; index < analysis.tokens.size(); ++index) {
        if (index != 0) {
            output << ",";
        }
        const auto& token = analysis.tokens[index];
        output << "{\"text\":\"" << json_escape(token.text)
               << "\",\"category\":\""
               << token_category_name(token.category)
               << "\",\"range\":";
        write_range(output, token.range);
        output << "}";
    }
    output << "]}\n";
}

} // namespace

int main(int argc, char* argv[]) {
    if (argc == 2 && std::string_view(argv[1]) == "--analyze-json") {
        std::ostringstream source;
        source << std::cin.rdbuf();
        write_analysis_json(
            std::cout,
            proofassistant::analyze(source.str())
        );
        return 0;
    } else if (argc == 2) {
        return proofassistant::run_file(argv[1], std::cout, std::cerr);
    } else if (argc >= 3 && std::string_view(argv[1]) == "--latex") {
        std::optional<std::string> input_path;
        std::optional<std::string> output_path;

        for (int index = 2; index < argc; ++index) {
            const std::string_view argument = argv[index];
            if (argument == "-o") {
                if (output_path) {
                    std::cerr << "Error: '-o' may only be specified once.\n";
                    return 1;
                } else if (index + 1 >= argc) {
                    std::cerr << "Error: '-o' requires an output file path.\n";
                    return 1;
                } else {
                    output_path = argv[++index];
                }
            } else if (!input_path) {
                input_path = argument;
            } else {
                std::cerr
                    << "Error: multiple input files were specified: '"
                    << *input_path << "' and '" << argument << "'.\n";
                return 1;
            }
        }

        if (!input_path) {
            std::cerr << "Error: --latex requires an input file path.\n";
            return 1;
        } else if (!output_path) {
            return proofassistant::run_latex_file(
                *input_path,
                std::cout,
                std::cerr
            );
        } else {
            std::ofstream output{*output_path};
            if (!output.is_open()) {
                std::cerr
                    << "Error: could not open LaTeX output file '"
                    << *output_path << "'.\n";
                return 1;
            } else {
                return proofassistant::run_latex_file(
                    *input_path,
                    output,
                    std::cerr
                );
            }
        }
    } else {
        std::cerr
            << "Usage: " << argv[0] << " <input-file.n3>\n"
            << "       " << argv[0]
            << " --latex <input-file.n3> [-o <output-file.tex>]\n"
            << "       " << argv[0] << " --analyze-json < source.n3\n";
        return 1;
    }
}
