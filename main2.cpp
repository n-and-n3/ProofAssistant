#include <iostream>
#include <vector>
#include <string>
#include <cmath>
#include <set>
#include <unordered_map>
#include <map>
#include <unordered_set>
#include <queue>
#include <algorithm>
#include <iomanip>
#include <functional>
#include <cassert>
#include <bit>
#include <array>
#include <random>
#include <stack>
#include <stdexcept>
#include <memory>
#include <fstream>
#include <iterator>
#include <optional>

using namespace std;

#define ll long long
#define LL __int128
#define ld long double
#define INF 2251799813685248
#define rep(i, n) for (ll i = 0; i < (n); ++i)
#define reps(i, l, r) for(ll i = (l); i < (r); ++i)
#define foreach(c, A) for(auto c:(A))
#define vall(A) (A).begin(),(A).end()
#define vrall(A) (A).rbegin(),(A).rend()
#define slice(A, l, r) next((A).begin(), (l)), next((A).begin(), (r))
#define vin(A) for (ll iiii = 0, szszszsz = (A).size(); iiii < szszszsz; iiii++){cin >> (A)[iiii];}
#define vout(A) for (ll iiii = 0, szszszsz = (A).size(); iiii < szszszsz; iiii++){cout << (A)[iiii] << " \n"[iiii == szszszsz-1];}
#define vin2d(A) for (ll iiii = 0; iiii < (A).size(); iiii++){for (ll jjjj = 0; jjjj < (A)[iiii].size(); jjjj++){cin >> (A)[iiii][jjjj];}}
#define vout2d(A) for (ll iiii = 0; iiii < (A).size(); iiii++){for (ll jjjj = 0; jjjj < (A)[iiii].size(); jjjj++){cout << (A)[iiii][jjjj] << " \n"[jjjj==(A)[iiii].size()-1];}}
#define encode(i,j) (((i))<<32)+(j)
#define decode(v,w) ((w) ? (v)%4294967296 : (v)>>32)
#define vinc(A) for (auto &vvvv : (A)){vvvv++;}
#define vdec(A) for (auto &vvvv : (A)){vvvv--;}
#define graphin0(C, M) int aaaa,bbbb;for (int iiii = 0; iiii < (M); iiii++){cin >> aaaa >> bbbb; (C)[aaaa].push_back(bbbb); (C)[bbbb].push_back(aaaa);}
#define graphin1(C, M) int aaaa,bbbb;for (int iiii = 0; iiii < (M); iiii++){cin >> aaaa >> bbbb; (C)[aaaa-1].push_back(bbbb-1); (C)[bbbb-1].push_back(aaaa-1);}
#define lsegtype(name) name::S, name::F
#define lsegarg(name) name::op, name::e,name::comp, name::mapping, name::id

vector<ll> pow2ll{1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536,131072,262144,524288,1048576,2097152,4194304,8388608,16777216,33554432,67108864,134217728,268435456,536870912,1073741824,2147483648,4294967296,8589934592,17179869184,34359738368,68719476736,137438953472,274877906944,549755813888,1099511627776,2199023255552,4398046511104,8796093022208,17592186044416,35184372088832,70368744177664,140737488355328,281474976710656,562949953421312,1125899906842624,2251799813685248,4503599627370496,9007199254740992,18014398509481984,36028797018963968,72057594037927936,144115188075855872,288230376151711744,576460752303423488,1152921504606846976,2305843009213693952,4611686018427387904};
vector<ll> pow10ll{1,10,100,1000,10000,100000,1000000,10000000,100000000,1000000000,10000000000,100000000000,1000000000000,10000000000000,100000000000000,1000000000000000,10000000000000000,100000000000000000,1000000000000000000};
vector<ll> di{0,1,0,-1};
vector<ll> dj{1,0,-1,0};

template <typename T>
bool chmax(T &a, const T& b) { return a < b ? a = b, true : false; }
template <typename T>
bool chmin(T &a, const T& b) { return a > b ? a = b, true : false; }

unsigned int bit_length(ll n){ return n > 0 ? 64 - __builtin_clzll(n) : 0;}

template <typename T>
T sum(vector<T> A){
    T res = 0;
    for (size_t i=0;i<A.size();i++){
        res += A[i];
    }
    return res;
}

ll powll(ll a, ll n, ll m){
    if (n == 0){return 1;}
    if (n == 1){return a % m;}
    LL ans = 1;
    LL p = a;
    while(n > 0){
        if ((n & 1) == 1){
            ans *= p;
            ans %= m;
        }
        n >>= 1;
        p *= p;
        p %= m;
    }
    return (ll)ans;
}

// ===============================================================================

// 配列を特定の要素で区切る関数
vector<vector<string>> split(const vector<string>& tokens, const string& delimiter) {
    vector<vector<string>> result;
    vector<string> current;
    for (const auto& token : tokens) {
        if (token == delimiter) {
            if (!current.empty()) {
                result.push_back(current);
                current.clear();
            }
        } else {
            current.push_back(token);
        }
    }
    if (!current.empty()) {
        result.push_back(current);
    }
    return result;
}


// ===============================================================================


set<string> Logical_Connectives = {
    "*", "+", "->", "~"
};

auto precedence = [](const string& op) {
    if (op == "~") return 3;
    if (op == "*") return 2;
    if (op == "+") return 1;
    if (op == "->") return 0;
    return -1;
};

auto is_right_associative = [](const string& op) {
    return op == "->" || op == "~";
};


set<string> keywords = {
    "Type", "auto", "print"
};

set<string> Syntax_Symbols = {
    "(", ")", "{", "}", ";", ",", ":", "*", "+", "-", "<", ">", ";", "~", "[", "]", "|-", "="
};

set<string> inference_rules = {
    "andL", "andR", "orL", "orR", "impL", "impR", "notL", "notR", "Id", "KL", "KR", "cut"
};

unordered_map<string, int> inference_rule_arity = {
    {"andL", 1},
    {"andR", 2},
    {"orL", 2},
    {"orR", 1},
    {"impL", 2},
    {"impR", 1},
    {"notL", 1},
    {"notR", 1},
    {"Id", 0},
    {"KL", 1},
    {"KR", 1},
    {"cut", 2}
};

unordered_map<string, int> inference_rule_template_arity = {
    {"andL", 2},
    {"andR", 2},
    {"orL", 2},
    {"orR", 2},
    {"impL", 2},
    {"impR", 2},
    {"notL", 1},
    {"notR", 1},
    {"Id", 1},
    {"KL", 1},
    {"KR", 1},
    {"cut", 1}
};

enum SentenceType {
    Initialization, // None;
    PropDecl, // Type A;
    ProofDecl, // (A |- A) A_id = Id<A>();
    AutoDecl, // auto A_id = Id<A>();
    PrintStmt, // print A_id;
};

enum LogicalType {
    And, Or, Imp, Not, Var
};

enum class TokenKind {
    Identifier,
    Keyword,
    SyntaxSymbol,
    LogicalConnective,
    InferenceRule
};

struct SourceSpan {
    size_t start_line;
    size_t start_column;
    size_t end_line;
    size_t end_column;
};

struct Token {
    string text;
    TokenKind kind;
    SourceSpan source_span;

    operator const string&() const {
        return text;
    }

    bool operator==(string_view other) const {
        return text == other;
    }
};

bool operator==(string_view lhs, const Token& rhs) {
    return rhs == lhs;
}

ostream& operator<<(ostream& os, const Token& token) {
    return os << token.text;
}


// ================================================================================================

// プログラム全体をトークナイズする
vector<Token> tokenize(const string& code){
    vector<Token> tokens;

    vector<pair<size_t, size_t>> positions(code.size() + 1);
    size_t line = 1;
    size_t column = 1;
    for (size_t i = 0; i < code.size(); ++i) {
        positions[i] = {line, column};
        if (code[i] == '\n') {
            ++line;
            column = 1;
        } else {
            ++column;
        }
    }
    positions[code.size()] = {line, column};

    auto add_token = [&](size_t begin, size_t end) {
        if (begin >= end) {
            return;
        }
        string text = code.substr(begin, end - begin);
        TokenKind kind = TokenKind::Identifier;
        if (keywords.contains(text)) {
            kind = TokenKind::Keyword;
        } else if (inference_rules.contains(text)) {
            kind = TokenKind::InferenceRule;
        } else if (Logical_Connectives.contains(text)) {
            kind = TokenKind::LogicalConnective;
        } else if (Syntax_Symbols.contains(text)) {
            kind = TokenKind::SyntaxSymbol;
        }
        tokens.push_back(Token{
            std::move(text),
            kind,
            SourceSpan{
                positions[begin].first,
                positions[begin].second,
                positions[end - 1].first,
                positions[end - 1].second
            }
        });
    };

    size_t pos = 0;
    for (size_t i = 0; i <= code.size(); i++) {
        // `//` starts a line comment. Flush the token before it, then skip
        // everything through the newline (or through EOF).
        if (i + 1 < code.size() && code[i] == '/' && code[i + 1] == '/') {
            add_token(pos, i);
            size_t comment_end = i + 2;
            while (comment_end < code.size() && code[comment_end] != '\n') {
                ++comment_end;
            }
            if (comment_end < code.size()) {
                pos = comment_end + 1;
                i = comment_end;
            } else {
                pos = code.size();
                i = code.size();
            }
            continue;
        }

        // 2文字トークンを優先して切り出す
        if (i + 1 < code.size()) {
            if (code[i] == '|' && code[i + 1] == '-') {
                add_token(pos, i);
                add_token(i, i + 2);
                i++;            // '-' をスキップ
                pos = i + 1;     // 次の走査開始位置を更新
                continue;
            }
            if (code[i] == '-' && code[i + 1] == '>') {
                add_token(pos, i);
                add_token(i, i + 2);
                i++;            // '>' をスキップ
                pos = i + 1;     // 次の走査開始位置を更新
                continue;
            }
        }
        if (i == code.size() || code[i] == ' ' || code[i] == '\t' || code[i] == '\r' || code[i] == '\n' || Syntax_Symbols.count(string(1, code[i]))) {
            add_token(pos, i);
            if (i < code.size() && Syntax_Symbols.contains(string(1, code[i]))) {
                add_token(i, i + 1);
            }
            pos = i + 1;
        }
    }
    return tokens;
}



// =======================================================================================


struct ASTNode{
    string kind;
    string content;
    vector<shared_ptr<ASTNode>> children;
    optional<SourceSpan> source_span;

    ASTNode(
        string _nodetype,
        string _content,
        vector<shared_ptr<ASTNode>> _children = {},
        optional<SourceSpan> _source_span = nullopt
    ) : kind(std::move(_nodetype)),
        content(std::move(_content)),
        children(std::move(_children)),
        source_span(_source_span) {
        for (const auto& child : children) {
            if (!child || !child->source_span) {
                continue;
            }
            if (!source_span) {
                source_span = child->source_span;
                continue;
            }
            const auto& child_span = *child->source_span;
            if (pair{child_span.start_line, child_span.start_column} <
                pair{source_span->start_line, source_span->start_column}) {
                source_span->start_line = child_span.start_line;
                source_span->start_column = child_span.start_column;
            }
            if (pair{child_span.end_line, child_span.end_column} >
                pair{source_span->end_line, source_span->end_column}) {
                source_span->end_line = child_span.end_line;
                source_span->end_column = child_span.end_column;
            }
        }
    }


    static size_t hash_combine(size_t seed, size_t value) {
        seed ^= value + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2);
        return seed;
    }

    size_t compute_hash() const {
        size_t seed = std::hash<string>{}(kind);
        seed = hash_combine(seed, std::hash<string>{}(content));
        for (const auto& child : children) {
            seed = hash_combine(seed, child ? child->compute_hash() : 0);
        }
        return seed;
    }

    string to_string() const {
        if (kind == "type_identifier") {
            return content;
        } else if (kind == "prop_identifier") {
            return content;
        } else if (kind == "sequent_identifier") {
            return content;
        } else if (kind == "logical" && content == "not") {
            return "(~" + children[0]->to_string() + ")";
        } else if (kind == "logical" && (content == "and" || content == "or" || content == "imp")) {
            string op_str;
            if (kind == "logical" && content == "and") {
                op_str = "*";
            } else if (kind == "logical" && content == "or") {
                op_str = "+";
            } else {
                op_str = "->";
            }
            return "(" + children[0]->to_string() + " " + op_str + " " + children[1]->to_string() + ")";
        } else {
            string res = kind + "(" + content + ")";
            if (!children.empty()) {
                res += " [";
                for (size_t i = 0; i < children.size(); ++i) {
                    res += children[i]->to_string();
                    if (i < children.size() - 1) {
                        res += ", ";
                    }
                }
                res += "]";
            }
            return res;
        }
    }

    static bool equals(const shared_ptr<const ASTNode>& a, const shared_ptr<const ASTNode>& b) {
        if (a == b) {
            return true;
        }
        if (!a || !b) {
            return false;
        }
        if (a->kind != b->kind || a->content != b->content || a->children.size() != b->children.size()) {
            return false;
        }
        for (size_t i = 0; i < a->children.size(); ++i) {
            if (!equals(a->children[i], b->children[i])) {
                return false;
            }
        }
        return true;
    }
};

// 命題そのもの（ASTNodeへの薄いラッパ）
struct Prop {
    shared_ptr<const ASTNode> root;
    size_t hash_value = 0;

    Prop() = default;

    explicit Prop(shared_ptr<const ASTNode> root) : root(std::move(root)), hash_value(this->root ? this->root->compute_hash() : 0) {}

    size_t hash() const noexcept {
        return hash_value;
    }

    string to_string() const {
        if (!root) {
            throw runtime_error("Internal error: empty Prop");
        }
        return root->to_string();
    }

    bool operator==(const Prop& other) const {
        if (hash_value != other.hash_value) {
            return false;
        }
        return ASTNode::equals(root, other.root);
    }
};

namespace std {
template <>
struct hash<Prop> {
    size_t operator()(const Prop& p) const noexcept {
        return p.hash();
    }
};
} // namespace std



struct Sequent {
    unordered_set<Prop> antecedent;
    unordered_set<Prop> succedent;

    Sequent() = default;
    Sequent(const unordered_set<Prop>& antecedent, const unordered_set<Prop>& succedent) : antecedent(antecedent), succedent(succedent) {}

    string to_string() const {
        string res;
        for (const auto& prop : antecedent) {
            res += prop.to_string();
            res += ", ";
        }
        res += " |- ";
        for (const auto& prop : succedent) {
            res += prop.to_string();
            res += ", ";
        }
        return res;
    }

    bool operator==(const Sequent& other) const {
        return antecedent == other.antecedent && succedent == other.succedent;
    }

    bool operator!=(const Sequent& other) const {
        return !(*this == other);
    }


};

struct Context{
    set<string> env_type;
    unordered_map<string, Sequent> env_sequent;
};

string format_source_span(const optional<SourceSpan>& source_span) {
    if (!source_span) {
        return "unknown location";
    }
    const auto& span = *source_span;
    return "line " + to_string(span.start_line) + ", column " +
        to_string(span.start_column) + " to line " +
        to_string(span.end_line) + ", column " +
        to_string(span.end_column);
}

[[noreturn]] void throw_validation_error(const ASTNode& node, const string& message) {
    throw runtime_error("Validation error at " + format_source_span(node.source_span) + ": " + message);
}

[[noreturn]] void throw_parse_error(
    const vector<Token>& tokens,
    int pc,
    const string& message
) {
    optional<SourceSpan> span = nullopt;
    if (pc >= 0 && pc < ssize(tokens)) {
        span = tokens[pc].source_span;
    } else if (!tokens.empty()) {
        span = tokens.back().source_span;
    }
    throw runtime_error("Parse error at " + format_source_span(span) + ": " + message);
}

const Token& require_current_token(
    const vector<Token>& tokens,
    int pc,
    const string& expected
) {
    if (pc < 0 || pc >= ssize(tokens)) {
        throw_parse_error(tokens, pc, "Expected " + expected + ", but reached the end of input.");
    } else {
        return tokens[pc];
    }
}

void require_token_text(
    const vector<Token>& tokens,
    int pc,
    string_view expected
) {
    require_current_token(
        tokens,
        pc,
        "token '" + string(expected) + "'"
    );
    const Token& actual = tokens[pc];
    if (actual.text != expected) {
        throw_parse_error(
            tokens,
            pc,
            "Expected token '" + string(expected) + "', but found '" +
                actual.text + "'."
        );
    }
}

void require_node_kind(const shared_ptr<ASTNode>& node, const string& expected_kind) {
    if (!node) {
        throw runtime_error("Validation error at unknown location: expected an AST node, but found null.");
    }
    if (node->kind != expected_kind) {
        throw_validation_error(
            *node,
            "Expected AST kind '" + expected_kind + "', but found '" +
                node->kind + "'."
        );
    }
}

void require_child_count(const shared_ptr<ASTNode>& node, size_t expected_count) {
    if (!node) {
        throw runtime_error("Validation error at unknown location: expected an AST node, but found null.");
    }
    if (node->children.size() != expected_count) {
        throw_validation_error(
            *node,
            "Expected " + to_string(expected_count) +
                " child node(s), but found " + to_string(node->children.size()) +
                "."
        );
    }
}

void require_identifier_available(
    const Context& context,
    const string& name,
    const ASTNode& identifier_node
) {
    if (context.env_type.contains(name) || context.env_sequent.contains(name)) {
        throw_validation_error(
            identifier_node,
            "Identifier '" + name + "' is already defined."
        );
    }
}

void require_type_defined(
    const Context& context,
    const string& name,
    const ASTNode& identifier_node
) {
    if (!context.env_type.contains(name)) {
        throw_validation_error(
            identifier_node,
            "Proposition variable '" + name + "' is not defined. Declare it with 'Type " +
                name + ";' before using it."
        );
    }
}

const Sequent& require_sequent_defined(
    const Context& context,
    const string& name,
    const ASTNode& identifier_node
) {
    auto it = context.env_sequent.find(name);
    if (it == context.env_sequent.end()) {
        throw_validation_error(
            identifier_node,
            "Sequent variable '" + name + "' is not defined."
        );
    }
    return it->second;
}

void declare_type(
    Context& context,
    const string& name,
    const ASTNode& identifier_node
) {
    require_identifier_available(context, name, identifier_node);
    context.env_type.insert(name);
}

void declare_sequent(
    Context& context,
    const string& name,
    const Sequent& value,
    const ASTNode& identifier_node
) {
    require_identifier_available(context, name, identifier_node);
    context.env_sequent.emplace(name, value);
}


// ========================================================================================
shared_ptr<ASTNode> parse_prop(const vector<Token> &tokens, int &pc);
shared_ptr<ASTNode> parse_type_expr(const vector<Token> &tokens, int &pc);


shared_ptr<ASTNode> parse_type_identifier(const vector<Token> &tokens, int &pc){
    require_current_token(tokens, pc, "a type identifier");
    if (!keywords.contains(tokens[pc]) && !Syntax_Symbols.contains(tokens[pc])){
        auto node = make_shared<ASTNode>("type_identifier", tokens[pc].text, vector<shared_ptr<ASTNode>>{}, tokens[pc].source_span);
        pc += 1;
        return node;
    } else {
        throw_parse_error(tokens, pc, "Expected a type identifier, but found '" + tokens[pc].text + "'.");
    }
}
shared_ptr<ASTNode> parse_prop_identifier(const vector<Token> &tokens, int &pc){
    require_current_token(tokens, pc, "a proposition identifier");
    if (!keywords.contains(tokens[pc]) && !Syntax_Symbols.contains(tokens[pc])){
        auto node = make_shared<ASTNode>("prop_identifier", tokens[pc].text, vector<shared_ptr<ASTNode>>{}, tokens[pc].source_span);
        pc += 1;
        return node;
    } else {
        throw_parse_error(tokens, pc, "Expected a proposition identifier, but found '" + tokens[pc].text + "'.");
    }
}

shared_ptr<ASTNode> parse_sequent_identifier(const vector<Token> &tokens, int &pc){
    require_current_token(tokens, pc, "a sequent identifier");
    if (!keywords.contains(tokens[pc]) && !Syntax_Symbols.contains(tokens[pc])){
        auto node = make_shared<ASTNode>(
            "sequent_identifier",
            tokens[pc].text,
            vector<shared_ptr<ASTNode>>{},
            tokens[pc].source_span
        );
        pc += 1;
        return node;
    } else {
        throw_parse_error(tokens, pc, "Expected a sequent identifier, but found '" + tokens[pc].text + "'.");
    }
}

shared_ptr<ASTNode> parse_expression(const vector<Token> &tokens, int &pc){
    // 関数式を解析する
    require_current_token(tokens, pc, "an inference rule or sequent identifier");
    // 関数一覧の要素 <型, 型, ...>(命題, 命題, ...)
    if (inference_rules.contains(tokens[pc])){
        SourceSpan rule_span = tokens[pc].source_span;
        string rule_name = tokens[pc];
        pc += 1;
        require_token_text(tokens, pc, "<");
        pc += 1;
        vector<shared_ptr<ASTNode>> type_args;
        rep(_, inference_rule_template_arity[rule_name]){
            type_args.push_back(parse_type_expr(tokens, pc));
            if (pc < ssize(tokens) && tokens[pc] == ","){
                pc += 1; // skip ','
            }
        }
        require_token_text(tokens, pc, ">");
        pc += 1; // skip '>'
        require_token_text(tokens, pc, "(");
        pc += 1; // skip '('
        vector<shared_ptr<ASTNode>> prop_args;
        rep(_, inference_rule_arity[rule_name]){
            prop_args.push_back(parse_expression(tokens, pc));
            if (pc < ssize(tokens) && tokens[pc] == ","){
                pc += 1; // skip ','
            }
        }
        require_token_text(tokens, pc, ")");
        pc += 1; // skip ')'
        auto node = make_shared<ASTNode>(
            "inference_rules",
            rule_name,
            vector<shared_ptr<ASTNode>>{
                make_shared<ASTNode>("type_args", "", std::move(type_args)),
                make_shared<ASTNode>("prop_args", "", std::move(prop_args))
            },
            rule_span
        );
        return node;
    }

    // identifier の場合
    if (!keywords.contains(tokens[pc]) && !Syntax_Symbols.contains(tokens[pc])){
        auto tmp = parse_sequent_identifier(tokens, pc);
        return tmp;
    }

    throw_parse_error(
        tokens,
        pc,
        "Expected an inference rule or sequent identifier, but found '" +
            tokens[pc].text + "'."
    );
}


shared_ptr<ASTNode> parse_factor(const vector<Token> &tokens, int &pc){
    // parse_factor
    require_current_token(tokens, pc, "a proposition");
    if (tokens[pc] == "("){
        pc += 1;
        auto tmp = parse_prop(tokens, pc);
        require_token_text(tokens, pc, ")");
        pc += 1;
        return tmp;
    } else {
        return parse_prop_identifier(tokens, pc);
    }
}

shared_ptr<ASTNode> parse_not(const vector<Token> &tokens, int &pc){
    // ~ parse_factor
    require_current_token(tokens, pc, "a proposition");
    if (tokens[pc] == "~"){
        SourceSpan not_span = tokens[pc].source_span;
        pc += 1;
        auto tmp = parse_not(tokens, pc);
        return make_shared<ASTNode>("logical", "not", vector<shared_ptr<ASTNode>>{tmp}, not_span);
    } else {
        auto tmp = parse_factor(tokens, pc);
        return tmp;
    }
}


shared_ptr<ASTNode> parse_and(const vector<Token> &tokens, int &pc){
    // parse_not * parse_and
    require_current_token(tokens, pc, "a proposition");
    auto left = parse_not(tokens, pc);
    while (pc < ssize(tokens) && tokens[pc] == "*"){
        pc += 1;
        auto right = parse_not(tokens, pc);
        left = make_shared<ASTNode>("logical", "and", vector<shared_ptr<ASTNode>>{left, right});
    }
    return left;
}


shared_ptr<ASTNode> parse_or(const vector<Token> &tokens, int &pc){
    // parse_or + parse_and
    require_current_token(tokens, pc, "a proposition");
    auto left = parse_and(tokens, pc);
    while (pc < ssize(tokens) && tokens[pc] == "+"){
        pc += 1;
        auto right = parse_and(tokens, pc);
        left = make_shared<ASTNode>("logical", "or", vector<shared_ptr<ASTNode>>{left, right});
    }
    return left;
}


shared_ptr<ASTNode> parse_imp(const vector<Token> &tokens, int &pc){
    // parse_or -> parse_imp
    require_current_token(tokens, pc, "a proposition");
    auto left = parse_or(tokens, pc);
    if (pc < ssize(tokens) && tokens[pc] == "->"){
        pc += 1;
        auto right = parse_imp(tokens, pc);
        return make_shared<ASTNode>("logical", "imp", vector<shared_ptr<ASTNode>>{left, right});
    }
    return left;
}

shared_ptr<ASTNode> parse_prop(const vector<Token> &tokens, int &pc){
    // parse_imp
    require_current_token(tokens, pc, "a proposition");
    return parse_imp(tokens, pc);
}

shared_ptr<ASTNode> parse_type_expr(const vector<Token> &tokens, int &pc){
    // type template argument is parsed with the same grammar as propositions
    return parse_prop(tokens, pc);
}


shared_ptr<ASTNode> parse_propargs(const vector<Token> &tokens, int &pc){
    // prop, prop, ...
    require_current_token(tokens, pc, "a proposition list or its terminator");
    auto main = make_shared<ASTNode>("propargs", "");
    if (pc >= ssize(tokens) || tokens[pc] == "|-" || tokens[pc] == "]" || tokens[pc] == ")" || tokens[pc] == ";"){
        return main;
    }
    main->children.push_back(parse_prop(tokens, pc));
    while (pc < ssize(tokens) && tokens[pc] == ","){
        pc += 1;
        main->children.push_back(parse_prop(tokens, pc));
    }
    return main;

}

shared_ptr<ASTNode> parse_sequent(const vector<Token> &tokens, int &pc){
    // propargs |- propargs
    require_current_token(tokens, pc, "a sequent");
    auto tmp1 = parse_propargs(tokens, pc);
    require_token_text(tokens, pc, "|-");
    pc += 1;
    auto tmp2 = parse_propargs(tokens, pc);
    auto node = make_shared<ASTNode>("sequent", "", vector<shared_ptr<ASTNode>>{tmp1, tmp2});
    return node;
}

shared_ptr<ASTNode> parse_code(const vector<Token> &tokens, int &pc){
    auto main = make_shared<ASTNode>("code", "");
    while (pc < ssize(tokens)){
        SourceSpan key_span = tokens[pc].source_span;
        string key = tokens[pc];
        if (key == ";"){
            while (pc < ssize(tokens) && tokens[pc] == ";"){
                pc += 1;
            }
        } else {
            if (key == "print"){
                // print identifier;
                pc += 1;
                auto tmp = parse_sequent_identifier(tokens, pc);
                auto state = make_shared<ASTNode>("prefix", "print", vector<shared_ptr<ASTNode>>{tmp}, key_span);
                main->children.push_back(state);
                require_token_text(tokens, pc, ";");
                pc += 1;
            } else if (key == "Type"){
                // Type identifier;
                pc += 1;
                auto tmp = parse_type_identifier(tokens, pc);
                auto state = make_shared<ASTNode>("prefix", "Type", vector<shared_ptr<ASTNode>>{tmp}, key_span);
                main->children.push_back(state);
                require_token_text(tokens, pc, ";");
                pc += 1;
            } else if (key == "auto"){
                // auto identifier = expression;
                pc += 1;
                auto tmp1 = parse_sequent_identifier(tokens, pc);
                require_token_text(tokens, pc, "=");
                pc += 1;
                auto tmp2 = parse_expression(tokens, pc);
                auto state = make_shared<ASTNode>("prefix", "auto", vector<shared_ptr<ASTNode>>{tmp1, tmp2}, key_span);
                main->children.push_back(state);
                require_token_text(tokens, pc, ";");
                pc += 1;
            } else if (key == "["){
                // [sequent] identifier = expression;
                pc += 1;
                auto tmp1 = parse_sequent(tokens, pc);
                require_token_text(tokens, pc, "]");
                pc += 1;
                auto tmp2 = parse_sequent_identifier(tokens, pc);
                require_token_text(tokens, pc, "=");
                pc += 1;
                auto tmp3 = parse_expression(tokens, pc);
                auto state = make_shared<ASTNode>("prefix", "var", vector<shared_ptr<ASTNode>>{tmp1, tmp2, tmp3}, key_span);
                main->children.push_back(state);
                require_token_text(tokens, pc, ";");
                pc += 1;
            } else {
                throw_parse_error(
                    tokens,
                    pc,
                    "Expected a statement beginning with 'Type', 'auto', 'print', or '[', but found '" +
                        tokens[pc].text + "'."
                );
            }
        }
    }


    // EoF
    if (pc == ssize(tokens)){
        return main;
    } else {
        throw_parse_error(
            tokens,
            pc,
            "Parser stopped before consuming the complete input."
        );
    }

}

void print_ast(const shared_ptr<ASTNode>& node, int depth = 0) {
    if (!node) return;
    cout << string(depth * 2, ' ') << node->kind << " " << node->content << "\n";
    for (auto child : node->children) {
        print_ast(child, depth + 1);
    }
}

shared_ptr<ASTNode> parser(const vector<Token>& tokens){
    int pc = 0;
    return parse_code(tokens, pc);
}

Prop evaluate_prop(const shared_ptr<ASTNode>& node, const Context& context);
Sequent evaluate_proof(const shared_ptr<ASTNode>& node, const Context& context);

shared_ptr<ASTNode> mutable_prop_root(const Prop& prop, const ASTNode& error_node) {
    if (!prop.root) {
        throw_validation_error(error_node, "An internal proposition has no AST root.");
    }
    return const_pointer_cast<ASTNode>(prop.root);
}

Prop make_unary_prop(
    const string& operation,
    const Prop& operand,
    const ASTNode& source_node
) {
    return Prop(make_shared<ASTNode>(
        "logical",
        operation,
        vector<shared_ptr<ASTNode>>{mutable_prop_root(operand, source_node)},
        source_node.source_span
    ));
}

Prop make_binary_prop(
    const string& operation,
    const Prop& left,
    const Prop& right,
    const ASTNode& source_node
) {
    return Prop(make_shared<ASTNode>(
        "logical",
        operation,
        vector<shared_ptr<ASTNode>>{
            mutable_prop_root(left, source_node),
            mutable_prop_root(right, source_node)
        },
        source_node.source_span
    ));
}

Prop evaluate_prop(const shared_ptr<ASTNode>& node, const Context& context) {
    if (!node) {
        throw runtime_error(
            "Validation error at unknown location: expected a proposition AST node, but found null."
        );
    }

    if (node->kind == "prop_identifier") {
        require_child_count(node, 0);
        if (node->content.empty()) {
            throw_validation_error(*node, "A proposition identifier cannot be empty.");
        } else {
            require_type_defined(context, node->content, *node);
            return Prop(node);
        }
    } else if (node->kind == "logical") {
        if (node->content == "not") {
            require_child_count(node, 1);
            evaluate_prop(node->children[0], context);
            return Prop(node);
        } else if (
            node->content == "and" ||
            node->content == "or" ||
            node->content == "imp"
        ) {
            require_child_count(node, 2);
            evaluate_prop(node->children[0], context);
            evaluate_prop(node->children[1], context);
            return Prop(node);
        } else {
            throw_validation_error(
                *node,
                "Unknown logical operation '" + node->content + "'."
            );
        }
    } else {
        throw_validation_error(
            *node,
            "Expected a proposition node with kind 'prop_identifier' or 'logical', but found '" +
                node->kind + "'."
        );
    }
}

unordered_set<Prop> evaluate_propargs(
    const shared_ptr<ASTNode>& node,
    const Context& context
) {
    require_node_kind(node, "propargs");
    unordered_set<Prop> result;
    for (const auto& child : node->children) {
        result.insert(evaluate_prop(child, context));
    }
    return result;
}

Sequent evaluate_sequent(const shared_ptr<ASTNode>& node, const Context& context) {
    require_node_kind(node, "sequent");
    require_child_count(node, 2);
    auto antecedent = evaluate_propargs(node->children[0], context);
    auto succedent = evaluate_propargs(node->children[1], context);
    return Sequent(antecedent, succedent);
}

Sequent apply_inference_rule(
    const shared_ptr<ASTNode>& rule_node,
    const vector<Prop>& template_args,
    const vector<Sequent>& premises
) {
    require_node_kind(rule_node, "inference_rules");
    const string& rule = rule_node->content;

    if (!inference_rule_template_arity.contains(rule)) {
        throw_validation_error(*rule_node, "Unknown inference rule '" + rule + "'.");
    } else if (!inference_rule_arity.contains(rule)) {
        throw_validation_error(
            *rule_node,
            "Inference rule '" + rule + "' has no registered premise arity."
        );
    } else if (
        template_args.size() !=
        static_cast<size_t>(inference_rule_template_arity.at(rule))
    ) {
        throw_validation_error(
            *rule_node,
            "Inference rule '" + rule + "' expects " +
                to_string(inference_rule_template_arity.at(rule)) +
                " template argument(s), but received " +
                to_string(template_args.size()) + "."
        );
    } else if (
        premises.size() != static_cast<size_t>(inference_rule_arity.at(rule))
    ) {
        throw_validation_error(
            *rule_node,
            "Inference rule '" + rule + "' expects " +
                to_string(inference_rule_arity.at(rule)) +
                " premise(s), but received " + to_string(premises.size()) + "."
        );
    }

    if (rule == "Id") {
        const Prop& prop = template_args[0];
        return Sequent({prop}, {prop});
    } else if (rule == "KL") {
        auto antecedent = premises[0].antecedent;
        antecedent.insert(template_args[0]);
        return Sequent(antecedent, premises[0].succedent);
    } else if (rule == "KR") {
        auto succedent = premises[0].succedent;
        succedent.insert(template_args[0]);
        return Sequent(premises[0].antecedent, succedent);
    } else if (rule == "andL") {
        const Prop& left = template_args[0];
        const Prop& right = template_args[1];
        auto antecedent = premises[0].antecedent;
        if (!antecedent.contains(left)) {
            throw_validation_error(
                *rule_node,
                "andL requires its premise antecedent to contain the first template argument '" +
                    left.to_string() + "'."
            );
        } else if (!antecedent.contains(right)) {
            throw_validation_error(
                *rule_node,
                "andL requires its premise antecedent to contain the second template argument '" +
                    right.to_string() + "'."
            );
        } else {
            antecedent.erase(left);
            antecedent.erase(right);
            antecedent.insert(make_binary_prop("and", left, right, *rule_node));
            return Sequent(antecedent, premises[0].succedent);
        }
    } else if (rule == "andR") {
        const Prop& left = template_args[0];
        const Prop& right = template_args[1];
        if (premises[0].antecedent != premises[1].antecedent) {
            throw_validation_error(
                *rule_node,
                "andR requires both premise antecedents to be identical."
            );
        } else if (!premises[0].succedent.contains(left)) {
            throw_validation_error(
                *rule_node,
                "andR requires the first premise succedent to contain '" +
                    left.to_string() + "'."
            );
        } else if (!premises[1].succedent.contains(right)) {
            throw_validation_error(
                *rule_node,
                "andR requires the second premise succedent to contain '" +
                    right.to_string() + "'."
            );
        } else {
            auto first_rest = premises[0].succedent;
            auto second_rest = premises[1].succedent;
            first_rest.erase(left);
            second_rest.erase(right);
            if (first_rest != second_rest) {
                throw_validation_error(
                    *rule_node,
                    "andR requires both premise succedents to have identical remaining contexts."
                );
            } else {
                first_rest.insert(make_binary_prop("and", left, right, *rule_node));
                return Sequent(premises[0].antecedent, first_rest);
            }
        }
    } else if (rule == "orL") {
        const Prop& left = template_args[0];
        const Prop& right = template_args[1];
        if (premises[0].succedent != premises[1].succedent) {
            throw_validation_error(
                *rule_node,
                "orL requires both premise succedents to be identical."
            );
        } else if (!premises[0].antecedent.contains(left)) {
            throw_validation_error(
                *rule_node,
                "orL requires the first premise antecedent to contain '" +
                    left.to_string() + "'."
            );
        } else if (!premises[1].antecedent.contains(right)) {
            throw_validation_error(
                *rule_node,
                "orL requires the second premise antecedent to contain '" +
                    right.to_string() + "'."
            );
        } else {
            auto first_rest = premises[0].antecedent;
            auto second_rest = premises[1].antecedent;
            first_rest.erase(left);
            second_rest.erase(right);
            if (first_rest != second_rest) {
                throw_validation_error(
                    *rule_node,
                    "orL requires both premise antecedents to have identical remaining contexts."
                );
            } else {
                first_rest.insert(make_binary_prop("or", left, right, *rule_node));
                return Sequent(first_rest, premises[0].succedent);
            }
        }
    } else if (rule == "orR") {
        const Prop& left = template_args[0];
        const Prop& right = template_args[1];
        auto succedent = premises[0].succedent;
        if (!succedent.contains(left)) {
            throw_validation_error(
                *rule_node,
                "orR requires its premise succedent to contain the first template argument '" +
                    left.to_string() + "'."
            );
        } else if (!succedent.contains(right)) {
            throw_validation_error(
                *rule_node,
                "orR requires its premise succedent to contain the second template argument '" +
                    right.to_string() + "'."
            );
        } else {
            succedent.erase(left);
            succedent.erase(right);
            succedent.insert(make_binary_prop("or", left, right, *rule_node));
            return Sequent(premises[0].antecedent, succedent);
        }
    } else if (rule == "impL") {
        const Prop& left = template_args[0];
        const Prop& right = template_args[1];
        if (!premises[0].succedent.contains(left)) {
            throw_validation_error(
                *rule_node,
                "impL requires the first premise succedent to contain the antecedent '" +
                    left.to_string() + "'."
            );
        } else if (!premises[1].antecedent.contains(right)) {
            throw_validation_error(
                *rule_node,
                "impL requires the second premise antecedent to contain the consequent '" +
                    right.to_string() + "'."
            );
        } else {
            auto first_succedent_rest = premises[0].succedent;
            auto second_antecedent_rest = premises[1].antecedent;
            first_succedent_rest.erase(left);
            second_antecedent_rest.erase(right);
            if (premises[0].antecedent != second_antecedent_rest) {
                throw_validation_error(
                    *rule_node,
                    "impL requires the first antecedent to match the second antecedent after removing the consequent."
                );
            } else if (first_succedent_rest != premises[1].succedent) {
                throw_validation_error(
                    *rule_node,
                    "impL requires the second succedent to match the first succedent after removing the antecedent."
                );
            } else {
                second_antecedent_rest.insert(
                    make_binary_prop("imp", left, right, *rule_node)
                );
                return Sequent(second_antecedent_rest, premises[1].succedent);
            }
        }
    } else if (rule == "impR") {
        const Prop& left = template_args[0];
        const Prop& right = template_args[1];
        auto antecedent = premises[0].antecedent;
        auto succedent = premises[0].succedent;
        if (!antecedent.contains(left)) {
            throw_validation_error(
                *rule_node,
                "impR requires its premise antecedent to contain '" +
                    left.to_string() + "'."
            );
        } else if (!succedent.contains(right)) {
            throw_validation_error(
                *rule_node,
                "impR requires its premise succedent to contain '" +
                    right.to_string() + "'."
            );
        } else {
            antecedent.erase(left);
            succedent.erase(right);
            succedent.insert(make_binary_prop("imp", left, right, *rule_node));
            return Sequent(antecedent, succedent);
        }
    } else if (rule == "notL") {
        const Prop& operand = template_args[0];
        auto antecedent = premises[0].antecedent;
        auto succedent = premises[0].succedent;
        if (!succedent.contains(operand)) {
            throw_validation_error(
                *rule_node,
                "notL requires its premise succedent to contain '" +
                    operand.to_string() + "'."
            );
        } else {
            succedent.erase(operand);
            antecedent.insert(make_unary_prop("not", operand, *rule_node));
            return Sequent(antecedent, succedent);
        }
    } else if (rule == "notR") {
        const Prop& operand = template_args[0];
        auto antecedent = premises[0].antecedent;
        auto succedent = premises[0].succedent;
        if (!antecedent.contains(operand)) {
            throw_validation_error(
                *rule_node,
                "notR requires its premise antecedent to contain '" +
                    operand.to_string() + "'."
            );
        } else {
            antecedent.erase(operand);
            succedent.insert(make_unary_prop("not", operand, *rule_node));
            return Sequent(antecedent, succedent);
        }

    } else if (rule == "cut") {
        // Γ, A ⊢ Δ   and   Γ ⊢ A, Δ   gives   Γ ⊢ Δ
        const Prop& cut_prop = template_args[0];
        if (!premises[0].succedent.contains(cut_prop)) {
            throw_validation_error(
                *rule_node,
                "cut requires the first premise succedent to contain '" +
                    cut_prop.to_string() + "'."
            );
        } else if (!premises[1].antecedent.contains(cut_prop)) {
            throw_validation_error(
                *rule_node,
                "cut requires the second premise antecedent to contain '" +
                    cut_prop.to_string() + "'."
            );
        } else {
            auto first_succedent_rest = premises[0].succedent;
            auto second_antecedent_rest = premises[1].antecedent;
            first_succedent_rest.erase(cut_prop);
            second_antecedent_rest.erase(cut_prop);
            if (premises[0].antecedent != second_antecedent_rest) {
                throw_validation_error(
                    *rule_node,
                    "cut requires the first antecedent to match the second antecedent after removing the cut proposition."
                );
            } else if (first_succedent_rest != premises[1].succedent) {
                throw_validation_error(
                    *rule_node,
                    "cut requires the second succedent to match the first succedent after removing the cut proposition."
                );
            } else {
                return Sequent(premises[0].antecedent, premises[1].succedent);
            }
        }
    } else {
        throw_validation_error(
            *rule_node,
            "Inference rule '" + rule + "' is registered but has no evaluator implementation."
        );
    }
}

Sequent evaluate_proof(const shared_ptr<ASTNode>& node, const Context& context) {
    if (!node) {
        throw runtime_error(
            "Validation error at unknown location: expected a proof AST node, but found null."
        );
    }

    if (node->kind == "sequent_identifier") {
        require_child_count(node, 0);
        if (node->content.empty()) {
            throw_validation_error(*node, "A sequent identifier cannot be empty.");
        } else {
            return require_sequent_defined(context, node->content, *node);
        }
    } else if (node->kind == "inference_rules") {
        require_child_count(node, 2);
        const auto& type_args_node = node->children[0];
        const auto& prop_args_node = node->children[1];
        require_node_kind(type_args_node, "type_args");
        require_node_kind(prop_args_node, "prop_args");

        vector<Prop> template_args;
        template_args.reserve(type_args_node->children.size());
        for (const auto& child : type_args_node->children) {
            template_args.push_back(evaluate_prop(child, context));
        }

        vector<Sequent> premises;
        premises.reserve(prop_args_node->children.size());
        for (const auto& child : prop_args_node->children) {
            premises.push_back(evaluate_proof(child, context));
        }

        return apply_inference_rule(node, template_args, premises);
    } else {
        throw_validation_error(
            *node,
            "Expected a proof node with kind 'sequent_identifier' or 'inference_rules', but found '" +
                node->kind + "'."
        );
    }
}

void evaluate_statement(const shared_ptr<ASTNode>& node, Context& context) {
    require_node_kind(node, "prefix");

    if (node->content == "Type") {
        require_child_count(node, 1);
        const auto& identifier = node->children[0];
        require_node_kind(identifier, "type_identifier");
        require_child_count(identifier, 0);
        if (identifier->content.empty()) {
            throw_validation_error(*identifier, "A type identifier cannot be empty.");
        } else {
            declare_type(context, identifier->content, *identifier);
        }
    } else if (node->content == "auto") {
        require_child_count(node, 2);
        const auto& identifier = node->children[0];
        require_node_kind(identifier, "sequent_identifier");
        require_child_count(identifier, 0);
        if (identifier->content.empty()) {
            throw_validation_error(*identifier, "A sequent identifier cannot be empty.");
        } else {
            require_identifier_available(context, identifier->content, *identifier);
            Sequent result = evaluate_proof(node->children[1], context);
            declare_sequent(context, identifier->content, result, *identifier);
        }
    } else if (node->content == "var") {
        require_child_count(node, 3);
        const auto& identifier = node->children[1];
        require_node_kind(identifier, "sequent_identifier");
        require_child_count(identifier, 0);
        if (identifier->content.empty()) {
            throw_validation_error(*identifier, "A sequent identifier cannot be empty.");
        } else {
            require_identifier_available(context, identifier->content, *identifier);
            Sequent expected = evaluate_sequent(node->children[0], context);
            Sequent actual = evaluate_proof(node->children[2], context);
            if (actual != expected) {
                throw_validation_error(
                    *node,
                    "Proof result does not match the declared sequent. Expected '" +
                        expected.to_string() + "', but derived '" +
                        actual.to_string() + "'."
                );
            } else {
                declare_sequent(context, identifier->content, actual, *identifier);
            }
        }
    } else if (node->content == "print") {
        require_child_count(node, 1);
        const auto& identifier = node->children[0];
        require_node_kind(identifier, "sequent_identifier");
        require_child_count(identifier, 0);
        if (identifier->content.empty()) {
            throw_validation_error(*identifier, "A sequent identifier cannot be empty.");
        } else {
            const Sequent& value = require_sequent_defined(
                context,
                identifier->content,
                *identifier
            );
            cout << "Proved : " << value.to_string() << "\n";
        }
    } else {
        throw_validation_error(
            *node,
            "Unknown statement type '" + node->content + "'."
        );
    }
}

void evaluate(const shared_ptr<ASTNode>& node, Context& context) {
    require_node_kind(node, "code");
    for (const auto& statement : node->children) {
        evaluate_statement(statement, context);
    }
}


int compile(const string& code) {
    vector<Token> tokens = tokenize(code);
    auto root = parser(tokens);
    Context context;
    evaluate(root, context);

    return 0;
}


// ===============================================================================
int main(int argc, char* argv[]) {
    if (argc != 2) {
        std::cerr << "Usage: " << argv[0] << " <input-file.n3>" << std::endl;
        return 1;
    }

    std::ifstream inputFile(argv[1]);

    if (!inputFile.is_open()) {
        std::cerr << "Error: could not open input file '" << argv[1] << "'." << std::endl;
        return 1; 
    }

    // --- ここからが一括読み込みの処理 ---
    std::stringstream buffer;
    buffer << inputFile.rdbuf(); // ファイルのバッファを全てstringstreamに流し込む
    std::string code = buffer.str(); // string型に変換
    // ------------------------------------

    try {
        int result = compile(code);
        cout << result << "\n";
        return result;
    } catch (const exception& error) {
        cerr << error.what() << "\n";
        return 1;
    } catch (...) {
        cerr << "Error: an unknown non-standard exception occurred.\n";
        return 1;
    }
}
