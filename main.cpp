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
    "(", ")", "{", "}", ";", ",", ":", "*", "+", "-", "<", ">", ";", "~"
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

// 命題のAST（ポインタ木部分）
struct ASTNode {
    LogicalType type;
    string name; // type == Var のときのみ有効
    shared_ptr<const ASTNode> left; // type == And, Or, Imp のときのみ有効
    shared_ptr<const ASTNode> right; // type == And, Or, Imp のときのみ有効
    shared_ptr<const ASTNode> operand; // type == Not のときのみ有効
    size_t hash_value;

    ASTNode(LogicalType type,
            string name = "",
            shared_ptr<const ASTNode> left = nullptr,
            shared_ptr<const ASTNode> right = nullptr,
            shared_ptr<const ASTNode> operand = nullptr)
        : type(type)
        , name(std::move(name))
        , left(std::move(left))
        , right(std::move(right))
        , operand(std::move(operand))
        , hash_value(compute_hash()) {}

    size_t hash() const noexcept {
        return hash_value;
    }

    // NOTE: 現時点では内部実装も参照しやすいよう public のままにしている。
    // 必要なら後で hash_combine/compute_hash を private に移す。
    static size_t hash_combine(size_t seed, size_t value) {
        seed ^= value + 0x9e3779b97f4a7c15ULL + (seed << 6) + (seed >> 2);
        return seed;
    }

    size_t compute_hash() const {
        size_t seed = std::hash<int>{}(static_cast<int>(type));
        if (type == Var) {
            return hash_combine(seed, std::hash<string>{}(name));
        }
        if (type == Not) {
            const size_t op_hash = operand ? operand->hash_value : 0;
            return hash_combine(seed, op_hash);
        }
        const size_t left_hash = left ? left->hash_value : 0;
        const size_t right_hash = right ? right->hash_value : 0;
        seed = hash_combine(seed, left_hash);
        seed = hash_combine(seed, right_hash);
        return seed;
    }

    string to_string() const {
        if (type == Var) {
            return name;
        } else if (type == Not) {
            return "(~" + operand->to_string() + ")";
        } else {
            string op_str = (type == And) ? "*" : (type == Or) ? "+" : "->";
            return "(" + left->to_string() + " " + op_str + " " + right->to_string() + ")";
        }
    }

    static bool equals(const shared_ptr<const ASTNode>& a, const shared_ptr<const ASTNode>& b) {
        if (a == b) {
            return true;
        }
        if (!a || !b) {
            return false;
        }
        if (a->type != b->type) {
            return false;
        }
        if (a->type == Var) {
            return a->name == b->name;
        }
        if (a->type == Not) {
            return equals(a->operand, b->operand);
        }
        return equals(a->left, b->left) && equals(a->right, b->right);
    }
};

// 命題そのもの（ASTNodeへの薄いラッパ）
struct Prop {
    shared_ptr<const ASTNode> root;
    size_t hash_value = 0;

    Prop() = default;

    explicit Prop(shared_ptr<const ASTNode> root) : root(std::move(root)), hash_value(this->root ? this->root->hash() : 0) {}

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

// それぞれのノード用のコンストラクタ（ASTを隠蔽してPropを返す）
Prop PropVar(const string& name) {
    const auto node = make_shared<ASTNode>(Var, name);
    return Prop(node);
}

Prop PropAnd(const Prop& left, const Prop& right) {
    const auto node = make_shared<ASTNode>(And, "", left.root, right.root);
    return Prop(node);
}

Prop PropOr(const Prop& left, const Prop& right) {
    const auto node = make_shared<ASTNode>(Or, "", left.root, right.root);
    return Prop(node);
}

Prop PropImp(const Prop& left, const Prop& right) {
    const auto node = make_shared<ASTNode>(Imp, "", left.root, right.root);
    return Prop(node);
}

Prop PropNot(const Prop& operand) {
    const auto node = make_shared<ASTNode>(Not, "", nullptr, nullptr, operand.root);
    return Prop(node);
}

struct Sequent {
    unordered_set<Prop> antecedent;
    unordered_set<Prop> succedent;

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

// =================================================================================================================
// 変数名の妥当性検査
auto validate_var(string name){
    if (name.empty() || !isalpha(name[0]) || keywords.count(name) != 0 || Logical_Connectives.count(name) != 0) {
        return false;
    } else {
        return true;
    }
}
// =================================================================================================================

// プログラム全体をトークナイズする
vector<string> tokenize(string code){
    vector<string> tokens;
    size_t pos = 0;
    for (size_t i = 0; i <= code.size(); i++) {
        if (i == code.size() || code[i] == ' ' || code[i] == '\n' || Syntax_Symbols.count(string(1, code[i]))) {
            if (pos < i) {
                tokens.push_back(code.substr(pos, i - pos));
            }
            if (i < code.size() && Syntax_Symbols.count(string(1, code[i]))) {
                tokens.push_back(string(1, code[i]));
            }
            pos = i + 1;
        }
    }
    return tokens;
}

// Propのtoken列を受け取り、RPNに変換する
vector<string> transform_to_RPN(const vector<string>& prop_expression, const set<string>& env){
    // Shunting yard algorithm
    stack<string> op_stack;
    vector<string> output_stack;

    for(auto token : prop_expression){
        if (env.count(token) != 0) {
            output_stack.push_back(token);
        } else if (Logical_Connectives.count(token) != 0) {
            while (!op_stack.empty() && Logical_Connectives.count(op_stack.top()) != 0) {
                const string& top = op_stack.top();
                if (precedence(top) > precedence(token) ||
                    (precedence(top) == precedence(token) && !is_right_associative(token))) {
                    output_stack.push_back(top);
                    op_stack.pop();
                } else {
                    break;
                }
            }
            op_stack.push(token);
        } else if (token == "(") {
            op_stack.push(token);
        } else if (token == ")") {
            while (!op_stack.empty() && op_stack.top() != "(") {
                output_stack.push_back(op_stack.top());
                op_stack.pop();
            }
            if (op_stack.empty() || op_stack.top() != "(") {
                throw runtime_error("Syntax error: mismatched parentheses");
            }
            op_stack.pop(); // "(" をポップ
        } else {
            throw runtime_error("Syntax error: unknown token '" + token + "'");
        }
    }

    while (!op_stack.empty()) {
        if (op_stack.top() == "(") {
            throw runtime_error("Syntax error: mismatched parentheses");
        }
        output_stack.push_back(op_stack.top());
        op_stack.pop();
    }

    return output_stack;

}

// RPNに変換された token列の Prop を計算する
Prop evaluate_Prop_expression(const vector<string>& prop_expression, const set<string>& env){
    vector<string> rpn = transform_to_RPN(prop_expression, env);
    if (rpn.empty()) {
        throw runtime_error("Syntax error: invalid expression");
    }
    vector<Prop> prop_stack;
    for (const auto& token : rpn) {
        cout << "RPN Token: " << token << "\n";
        if (env.count(token) != 0) {
            prop_stack.push_back(PropVar(token));
        } else if (token == "~") {
            if (prop_stack.empty()) {
                throw runtime_error("Syntax error: invalid expression");
            }
            Prop operand = prop_stack.back();
            prop_stack.pop_back();
            prop_stack.push_back(PropNot(operand));
        } else if (Logical_Connectives.count(token) != 0) {
            if (prop_stack.size() < 2) {
                throw runtime_error("Syntax error: invalid expression");
            }
            Prop right = prop_stack.back();
            prop_stack.pop_back();
            Prop left = prop_stack.back();
            prop_stack.pop_back();
            if (token == "*") {
                prop_stack.push_back(PropAnd(left, right));
            } else if (token == "+") {
                prop_stack.push_back(PropOr(left, right));
            } else if (token == "->") {
                prop_stack.push_back(PropImp(left, right));
            } else {
                throw runtime_error("Syntax error: unknown operator '" + token + "'");
            }
        } else {
            throw runtime_error("Syntax error: unknown token '" + token + "'");
        }
    }
    if (prop_stack.size() != 1) {
        throw runtime_error("Syntax error: invalid expression");

    }
    return prop_stack.back();
}

Sequent evaluate_proof_expression(const vector<string>& proof_expression, const set<string>& env_type, const unordered_map<string, Sequent>& env_prop){
    // NOTE: 現時点では証明の式の構文解析は未実装
    throw runtime_error("Proof expression parsing is not implemented yet");
}

// シークエントを表すトークン列を受け取って、Sequentオブジェクトを返す関数
Sequent parse_sequent(const vector<string>& sequent_tokens, const set<string>& env){
    // まずは |- を探す
    auto it = find(sequent_tokens.begin(), sequent_tokens.end(), "|-");
    if (it == sequent_tokens.end()) {
        throw runtime_error("Syntax error: expected '|-' in sequent\n");
    }
    vector<string> antecedent_tokens(sequent_tokens.begin(), it);
    vector<string> succedent_tokens(it + 1, sequent_tokens.end());

    // それぞれのトークン列を Prop オブジェクトに変換する
    unordered_set<Prop> antecedent;
    for (const auto& prop : split(antecedent_tokens, ",")) {
        antecedent.insert(evaluate_Prop_expression(prop, env));
    }

    unordered_set<Prop> succedent;
    for (const auto& prop : split(succedent_tokens, ",")) {
        succedent.insert(evaluate_Prop_expression(prop, env));
    }

    return Sequent(antecedent, succedent);
}

// 型宣言文を処理する関数
void match_type_statement(const vector<string>& tokens, int& pos, set<string>& env_type){
    int N = tokens.size();
    if (tokens[pos] != "Type") {
        throw runtime_error("Syntax error: expected 'Type' at the beginning of Type declaration\n");
    } else if (pos+1 >= N || !validate_var(tokens[pos+1])) {
        throw runtime_error("Syntax error: expected identifier after 'Type'\n");
    } else if (keywords.count(tokens[pos+1]) != 0) {
        throw runtime_error("Syntax error: '" + tokens[pos+1] + "' is a keyword\n");
    } else if (env_type.count(tokens[pos+1]) != 0) {
        throw runtime_error("Syntax error: duplicate Type declaration for '" + tokens[pos+1] + "'\n");
    } else if (pos + 2 >= N || tokens[pos + 2] != ";") { // 変数の後は ; である。
        throw runtime_error("Syntax error: expected ';' after Type declaration\n");
    } else {
        env_type.insert(tokens[pos+1]);
        pos += 3; // Typeと変数と ";" をスキップ
    }
}


// 型付きの推論規則を処理する関数
void match_proof_statement(const vector<string>& tokens, int& pos, set<string>& env_type, unordered_map<string, Sequent>& env_prop){
    int N = tokens.size();
    // 構文は `[シークエント] 変数名 = 証明のコード` とする

    // [ から始まる
    if (tokens[pos] != "[") {
        throw runtime_error("Syntax error: expected '[' at the beginning of proof declaration\n");
    }

    // ] を探す
    vector<string> sequent_tokens;
    while (pos < N && tokens[pos] != "]") {
        sequent_tokens.push_back(tokens[pos]);
        pos++;
    }
    if (pos >= N) {
        throw runtime_error("Syntax error: expected ']' at the end of sequent in proof declaration\n");
    }

    // ] の次は変数名であるべき
    pos++; // "]" をスキップ
    if (pos >= N || !validate_var(tokens[pos])) {
        throw runtime_error("Syntax error: expected identifier after ']' in proof declaration\n");
    }
    string argument_name = tokens[pos];

    if (env_type.count(argument_name) != 0){
        throw runtime_error("Syntax error: variable name '" + argument_name + "' is already declared as a Type\n");
    }
    if (env_prop.count(argument_name) != 0){
        throw runtime_error("Syntax error: duplicate declaration of argument '" + argument_name + "'\n");
    }

    // = が来る
    pos++;
    if (pos >= N || tokens[pos] != "="){
        throw runtime_error("Syntax error: expected '=' after argument name in proof declaration\n");
    }

    // ; までをスタックに積む
    vector<string> proof_stack;
    while (pos < N && tokens[pos] != ";") {
        proof_stack.push_back(tokens[pos]);
        pos++;
    }
    if (pos >= N) {
        throw runtime_error("Syntax error: expected ';' at the end of proof declaration\n");
    }
    pos++; // ";" をスキップ

    Sequent result = evaluate_proof_expression(proof_stack, env_type, env_prop);
    Sequent expected = parse_sequent(sequent_tokens, env_type);
    if (result != expected){
        throw runtime_error("Syntax error: proof expression does not match the expected sequent\n");
    }

    env_prop.emplace(argument_name, result); // シークエントをパースして、環境に追加する
}

// autoの推論規則を処理する関数
void match_auto_statement(const vector<string>& tokens, int& pos, set<string>& env_type, unordered_map<string, Sequent>& env_prop){
    int N = tokens.size();
    // 構文は `auto 変数名 = 証明のコード` とする
    // auto から始まる
    if (tokens[pos] != "auto") {
        throw runtime_error("Syntax error: expected 'auto' at the beginning of auto declaration\n");
    }
    pos++;
    // 変数名が来るべき
    if (pos >= N || !validate_var(tokens[pos])) {
        throw runtime_error("Syntax error: expected identifier after 'auto' in auto declaration\n");
    }
    string argument_name = tokens[pos];

    if (env_type.count(argument_name) != 0){
        throw runtime_error("Syntax error: variable name '" + argument_name + "' is already declared as a Type\n");
    }
    if (env_prop.count(argument_name) != 0){
        throw runtime_error("Syntax error: duplicate declaration of argument '" + argument_name + "'\n");
    }

    // = が来る
    pos++;
    if (pos >= N || tokens[pos] != "="){
        throw runtime_error("Syntax error: expected '=' after argument name in proof declaration\n");
    }

    // ; までをスタックに積む
    vector<string> proof_stack;
    while (pos < N && tokens[pos] != ";") {
        proof_stack.push_back(tokens[pos]);
        pos++;
    }
    if (pos >= N) {
        throw runtime_error("Syntax error: expected ';' at the end of proof declaration\n");
    }
    pos++; // ";" をスキップ
    Sequent result = evaluate_proof_expression(proof_stack, env_type, env_prop);

    env_prop.emplace(argument_name, result); // シークエントをパースして、環境に追加する
}

void match_print_statement(const vector<string>& tokens, int& pos, set<string>& env_type, unordered_map<string, Sequent>& env_prop){
    int N = tokens.size();
    // 構文は `print 変数名;` とする
    if (tokens[pos] != "print") {
        throw runtime_error("Syntax error: expected 'print' at the beginning of print statement\n");
    }
    pos++;
    if (pos >= N || !validate_var(tokens[pos])) {
        throw runtime_error("Syntax error: expected identifier after 'print'\n");
    }
    string argument_name = tokens[pos];
    pos++;
    if (pos >= N || tokens[pos] != ";") {
        throw runtime_error("Syntax error: expected ';' at the end of print statement\n");
    }
    pos++; // ";" をスキップ

    if (env_prop.count(argument_name) == 0) {
        throw runtime_error("Syntax error: undefined proof variable '" + argument_name + "' in print statement\n");
    }

    cout << env_prop[argument_name].to_string() << "\n";
}

int compile(const string& code){
    vector<string> tokens = tokenize(code);

    set<string> env_type; // Typeで宣言された識別子（命題変数）の列挙
    unordered_map<string, Sequent> env_proof; // 証明(Sequent)の列挙（未使用/拡張予定）
    int N = tokens.size();


    int pos = 0;

    while (pos < N){
        if (tokens[pos] == "Type"){
            match_type_statement(tokens, pos, env_type);
        } else if (tokens[pos] == "["){
            match_proof_statement(tokens, pos, env_type, env_proof);
        } else if (tokens[pos] == "auto"){
            match_auto_statement(tokens, pos, env_type, env_proof);
        } else if (tokens[pos] == "print"){
            match_print_statement(tokens, pos, env_type, env_proof);
        } else if (tokens[pos] == ";"){
            pos++; // 空の文を許容する
        } else {
            throw runtime_error("Syntax error: unexpected token '" + tokens[pos] + "'\n");
        }
    }

    return 0; // とりあえず成功とする
}


int main(){
    ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    // ========= Write your code here! ============================================================================
                                    
    string code = "Type A;\n"
                  "Type B;\n";
                                  
    // ============================================================================================================

    vector<string> tokens = tokenize(code);
    for (const auto& token : tokens) {
        if (keywords.count(token)) {
            cout << "Keyword: " << token << "\n";
        } else if (Logical_Connectives.count(token)) {
            cout << "Logical Connective: " << token << "\n";
        } else {
            cout << "Identifier: " << token << "\n";
        }
    }

    Prop res = evaluate_Prop_expression({"A", "*","~" ,"B", "+","~", "C"}, {"A", "B", "C"});
    cout << "Evaluated Prop expression: " << res.to_string() << "\n";

    try {
        compile(code);
    } catch (const runtime_error& e) {
        cout << e.what() << "\n";
        return 1;
    }

}

/*
メタコード
struct Prop{
  // hoge
}

struct Sequent{
  vector<Prop> antecedent;
  vector<Prop> succedent;

  Sequent(Prop X, Prop Y){
    return Sequent({X}, {Y});
  }
}

Sequent Id<P : Prop>(){
  return Sequent(P, P);
}

Sequent KL<A : Prop>(S : Sequent){
    vector<Prop> new_antecedent = S.antecedent;
    vector<Prop> new_succedent = S.succedent;
    new_antecedent.push_back(A);

    return Sequent(new_antecedent, new_succedent);
}

Sequent KR<A : Prop>(S : Sequent){
    vector<Prop> new_antecedent = S.antecedent;
    vector<Prop> new_succedent = S.succedent;
    new_succedent.push_back(A);

    return Sequent(new_antecedent, new_succedent);
}

Sequent andL<A : Prop, B : Prop>(S : Sequent){
    assert(A in S.antecedent);
    assert(B in S.antecedent);

    vector<Prop> new_antecedent = S.antecedent;
    vector<Prop> new_succedent = S.succedent;
    new_succedent.push_back(A*B);

    return Sequent(new_antecedent, new_succedent);
}

Sequent andR<A : Prop, B : Prop>(S1 : Sequent, S2 : Sequent){
    assert(A in S1.succedent);
    assert(B in S2.succedent);
    assert(S1.antecedent == S2.antecedent);
    assert(S1.succedent - {A} == S2.succedent - {B});

    vector<Prop> new_antecedent = S1.antecedent;
    new_antecedent.insert(new_antecedent.end(), S2.antecedent.begin(), S2.antecedent.end());
    vector<Prop> new_succedent = S1.succedent;
    new_succedent.insert(new_succedent.end(), S2.succedent.begin(), S2.succedent.end());
    new_succedent.push_back(A*B);

    return Sequent(new_antecedent, new_succedent);
}

Sequent orL<A : Prop, B : Prop>(S1 : Sequent, S2 : Sequent){
    assert(A in S1.antecedent);
    assert(B in S2.antecedent);
    assert(S1.succedent == S2.succedent);
    assert(S1.antecedent - {A} == S2.antecedent - {B});

    vector<Prop> new_antecedent = S1.antecedent;
    new_antecedent.insert(new_antecedent.end(), S2.antecedent.begin(), S2.antecedent.end());
    vector<Prop> new_succedent = S1.succedent;
    new_succedent.insert(new_succedent.end(), S2.succedent.begin(), S2.succedent.end());
    new_antecedent.push_back(A+B);

    return Sequent(new_antecedent, new_succedent);
}

Sequent orR<A : Prop, B : Prop>(S : Sequent){
    assert(A in S.succedent)
    assert(B in S.succedent);

    vector<Prop> new_antecedent = S.antecedent;
    vector<Prop> new_succedent = S.succedent;
    new_succedent.push_back(A+B);

    return Sequent(new_antecedent, new_succedent);
}

Sequent impL<A : Prop, B : Prop>(S1 : Sequent, S2 : Sequent){
    assert(A in S1.succedent);
    assert(B in S2.antecedent);
    assert(S1.antecedent == S2.antecedent);
    assert(S1.succedent - {A} == S2.succedent - {B});

    vector<Prop> new_antecedent = S1.antecedent;
    new_antecedent.insert(new_antecedent.end(), S2.antecedent.begin(), S2.antecedent.end());
    vector<Prop> new_succedent = S1.succedent;
    new_succedent.insert(new_succedent.end(), S2.succedent.begin(), S2.succedent.end());
    new_antecedent.push_back(A->B);

    return Sequent(new_antecedent, new_succedent);
}

Sequent impR<A : Prop, B : Prop>(S : Sequent){
    assert(A in S.antecedent);
    assert(B in S.succedent);

    vector<Prop> new_antecedent = S.antecedent;
    vector<Prop> new_succedent = S.succedent;
    new_succedent.push_back(A->B);

    return Sequent(new_antecedent, new_succedent);
}

Sequent notR<A : Prop>(S : Sequent){
    assert(A in S.antecedent);

    vector<Prop> new_antecedent = S.antecedent;
    vector<Prop> new_succedent = S.succedent;
    new_antecedent.erase(remove(new_antecedent.begin(), new_antecedent.end(), A), new_antecedent.end());
    new_succedent.push_back(not A);

    return Sequent(new_antecedent, new_succedent);
}

Sequent notL<A : Prop>(S : Sequent){
    assert(A in S.succedent);

    vector<Prop> new_antecedent = S.antecedent;
    vector<Prop> new_succedent = S.succedent;
    new_succedent.erase(remove(new_succedent.begin(), new_succedent.end(), A), new_succedent.end());
    new_antecedent.push_back(not A);

    return Sequent(new_antecedent, new_succedent);

*/

// $$ P \land (Q \lor R) \implies (P \land Q) \lor (P \land R) $$
// not (A * B) -> not A + not B


/*
Prop A;
Prop B;

auto A_id = Id<A>();
auto B_id = Id<B>();

auto AB_A = KL<B>(A_id);
auto AB_B = KL<A>(B_id);

auto AB_AB = andR<A, B>(AB_A, AB_B);
auto nAB_AB = notL<A*B>(AB_AB);
auto nAB_nA_nB = notR<A>(notR<B>(nAB_AB));

auto nAB_nAnB = orR<A, B>(nAB_nA_nB);

print nAB_nAnB;

*/

/*
           
    string code = "Prop A;\n"
                  "Prop B;\n"

                  "[A |- A] A_id = Id<A>();\n"
                  "auto B_id = Id<B>();\n"

                  "auto AB_A = KL<B>(A_id);\n"
                  "[B,A |- B] AB_B = KL<A>(B_id);\n"

                  "auto AB_AB = andR<A, B>(AB_A, AB_B);\""
                  "auto nAB_AB = notL<A*B>(AB_AB);\n"
                  "auto nAB_nA_nB = notR<A>(notR<B>(nAB_AB));\n"
                  "auto nAB_nAnB = orR<A, B>(nAB_nA_nB);\n"

                  "print nAB_nAnB;";

*/