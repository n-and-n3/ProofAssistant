CXX ?= g++
CXXFLAGS ?= -std=c++23 -O2 -Wall -Wextra

TARGET := main3
SOURCE := main3.cpp

.PHONY: all run test lsp extension-install clean

all: $(TARGET)

$(TARGET): $(SOURCE) main2.cpp proofassistant.cpp proofassistant.hpp
	$(CXX) $(CXXFLAGS) $(SOURCE) -o $(TARGET)

run: $(TARGET)
	./$(TARGET) proofs/iff.n3

test: $(TARGET)
	python3 -m unittest tests.test_main tests.test_lsp
	./$(TARGET) proofs/iff.n3

lsp:
	./scripts/build_lsp.sh

extension-install:
	./scripts/install_vscode_extension.sh

clean:
	rm -f $(TARGET)
