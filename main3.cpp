#define PROOFASSISTANT_IMPLEMENTATION
#include "proofassistant.hpp"

#include <fstream>
#include <iostream>
#include <optional>
#include <string>

int main(int argc, char* argv[]) {
    if (argc == 2) {
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
            << " --latex <input-file.n3> [-o <output-file.tex>]\n";
        return 1;
    }
}
