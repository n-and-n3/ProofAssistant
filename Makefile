CXX = g++
CXXFLAGS = -Wall -std=c++17

TARGET = main
SRC = main.cpp

$(TARGET): $(SRC)
	$(CXX) $(CXXFLAGS) -o $(TARGET) $(SRC)

run: $(TARGET)
	./$(TARGET)

clean:
	rm -f $(TARGET) $(TARGET).exe

.PHONY: lsp extension-install

lsp:
	./scripts/build_lsp.sh

extension-install:
	./scripts/install_vscode_extension.sh
