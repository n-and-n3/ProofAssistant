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
    "(", ")", "{", "}", ";", ",", ":", "*", "+", "-", "<", ">", ";", "~", "[", "]", "|-"
};

set<string> inference_rules = {
    "andL", "andR", "orL", "orR", "impL", "impR", "notL", "notR", "Id", "KL", "KR"
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
    {"KR", 1}
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
    {"KR", 1}
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

// =================================================================================================================
// 変数名の妥当性検査
auto validate_var(string name){
    if (name.empty() || !isalpha(name[0]) || keywords.count(name) != 0 || Logical_Connectives.count(name) != 0) {
        return false;
    } else {
        return true;
    }
}

int uuid = 0; // 内部的に使用する変数名を生成するためのカウンタ

string get_unique_var_name(){
    return "_" + to_string(uuid++);
}
// =================================================================================================================

Sequent apply_andL(Prop A, Prop B, Sequent sequent){
    // A, B, Γ |- Δ から A * B, Γ |- Δ を導出する
    unordered_set<Prop> new_antecedent = sequent.antecedent;
    if (new_antecedent.find(A) == new_antecedent.end()){
        throw runtime_error("Inference error: antecedent does not contain " + A.to_string() + " in apply_andL");
    }
    if (new_antecedent.find(B) == new_antecedent.end()){
        throw runtime_error("Inference error: antecedent does not contain " + B.to_string() + " in apply_andL");
    }
    new_antecedent.erase(A);
    new_antecedent.erase(B);
    new_antecedent.insert(PropAnd(A, B));
    return Sequent(new_antecedent, sequent.succedent);
}

Sequent apply_andR(Prop A, Prop B, Sequent sequent1, Sequent sequent2){
    // Γ |- Δ, A と Γ |- Δ, B から Γ |- Δ, A * B を導出する
    if (sequent1.antecedent != sequent2.antecedent) {
        throw runtime_error("Inference error: antecedents do not match in apply_andR");
    }
    if (sequent1.succedent.find(A) == sequent1.succedent.end()) {
        throw runtime_error("Inference error: succedent of first sequent does not contain " + A.to_string() + " in apply_andR");
    }
    if (sequent2.succedent.find(B) == sequent2.succedent.end()) {
        throw runtime_error("Inference error: succedent of second sequent does not contain " + B.to_string() + " in apply_andR");
    }
    unordered_set<Prop> new_succedent1 = sequent1.succedent;
    unordered_set<Prop> new_succedent2 = sequent2.succedent;
    new_succedent1.erase(A);
    new_succedent2.erase(B);
    if (new_succedent1 != new_succedent2) {
        throw runtime_error("Inference error: succedents do not match after erasing A and B in apply_andR");
    }
    new_succedent1.insert(PropAnd(A, B));
    return Sequent(sequent1.antecedent, new_succedent1);
}

Sequent apply_orL(Prop A, Prop B, Sequent sequent1, Sequent sequent2){
    // A, Γ |- Δ と B, Γ |- Δ から A + B, Γ |- Δ を導出する
    if (sequent1.succedent != sequent2.succedent) {
        throw runtime_error("Inference error: succedents do not match in apply_orL");
    }
    if (sequent1.antecedent.find(A) == sequent1.antecedent.end()) {
        throw runtime_error("Inference error: antecedent of first sequent does not contain " + A.to_string() + " in apply_orL");
    }
    if (sequent2.antecedent.find(B) == sequent2.antecedent.end()) {
        throw runtime_error("Inference error: antecedent of second sequent does not contain " + B.to_string() + " in apply_orL");
    }
    unordered_set<Prop> new_antecedent1 = sequent1.antecedent;
    unordered_set<Prop> new_antecedent2 = sequent2.antecedent;
    new_antecedent1.erase(A);
    new_antecedent2.erase(B);
    if (new_antecedent1 != new_antecedent2) {
        throw runtime_error("Inference error: antecedents do not match after erasing A and B in apply_orL");
    }
    new_antecedent1.insert(PropOr(A, B));
    return Sequent(new_antecedent1, sequent1.succedent);
}

Sequent apply_orR(Prop A, Prop B, Sequent sequent){
    // Γ |- Δ, A, B から Γ |- Δ, A + B を導出する
    unordered_set<Prop> new_succedent = sequent.succedent;
    if (new_succedent.find(A) == new_succedent.end()){
        throw runtime_error("Inference error: succedent does not contain " + A.to_string() + " in apply_orR");
    }
    if (new_succedent.find(B) == new_succedent.end()){
        throw runtime_error("Inference error: succedent does not contain " + B.to_string() + " in apply_orR");
    }
    new_succedent.erase(A);
    new_succedent.erase(B);
    new_succedent.insert(PropOr(A, B));
    return Sequent(sequent.antecedent, new_succedent);
}

Sequent apply_impL(Prop A, Prop B, Sequent sequent1, Sequent sequent2){
    // Γ |- Δ, A と B, Γ |- Δ から A -> B, Γ |- Δ を導出する
    if (sequent1.succedent.find(A) == sequent1.succedent.end()) {
        throw runtime_error("Inference error: succedent of first sequent does not contain " + A.to_string() + " in apply_impL");
    }
    if (sequent2.antecedent.find(B) == sequent2.antecedent.end()) {
        throw runtime_error("Inference error: antecedent of second sequent does not contain " + B.to_string() + " in apply_impL");
    }
    unordered_set<Prop> new_succedent1 = sequent1.succedent;
    unordered_set<Prop> new_antecedent2 = sequent2.antecedent;
    new_succedent1.erase(A);
    new_antecedent2.erase(B);
    if (sequent1.antecedent != new_antecedent2 || new_succedent1 != sequent2.succedent) {
        throw runtime_error("Inference error: antecedents or succedents do not match after erasing A and B in apply_impL");
    }
    new_antecedent2.insert(PropImp(A, B));
    return Sequent(new_antecedent2, sequent2.succedent);
}

Sequent apply_impR(Prop A, Prop B, Sequent sequent){
    // A, Γ |- Δ, B から Γ |- Δ, A -> B を導出する
    unordered_set<Prop> new_antecedent = sequent.antecedent;
    unordered_set<Prop> new_succedent = sequent.succedent;
    if (new_antecedent.find(A) == new_antecedent.end()){
        throw runtime_error("Inference error: antecedent does not contain " + A.to_string() + " in apply_impR");
    }
    if (new_succedent.find(B) == new_succedent.end()){
        throw runtime_error("Inference error: succedent does not contain " + B.to_string() + " in apply_impR");
    }
    new_antecedent.erase(A);
    new_succedent.erase(B);
    new_succedent.insert(PropImp(A, B));
    return Sequent(new_antecedent, new_succedent);
}

Sequent apply_notL(Prop A, Sequent sequent){
    // Γ |- Δ, A から ~A, Γ |- Δ を導出する
    unordered_set<Prop> new_antecedent = sequent.antecedent;
    unordered_set<Prop> new_succedent = sequent.succedent;
    if (new_succedent.find(A) == new_succedent.end()){
        throw runtime_error("Inference error: succedent does not contain " + A.to_string() + " in apply_notL");
    }
    new_succedent.erase(A);
    new_antecedent.insert(PropNot(A));
    return Sequent(new_antecedent, new_succedent);

}

Sequent apply_notR(Prop A, Sequent sequent){
    // Γ,A |- Δ から Γ |- Δ, ~A を導出する
    unordered_set<Prop> new_antecedent = sequent.antecedent;
    unordered_set<Prop> new_succedent = sequent.succedent;
    if (new_antecedent.find(A) == new_antecedent.end()){
        throw runtime_error("Inference error: antecedent does not contain " + A.to_string() + " in apply_notR");
    }
    new_antecedent.erase(A);
    new_succedent.insert(PropNot(A));
    return Sequent(new_antecedent, new_succedent);
}

Sequent apply_Id(Prop A){
    // A |- A を導出する
    return Sequent({A}, {A});
}

Sequent apply_KL(Prop A, Sequent sequent){
    // Γ |- Δ から Γ, A |- Δ を導出する
    unordered_set<Prop> new_antecedent = sequent.antecedent;
    new_antecedent.insert(A);
    return Sequent(new_antecedent, sequent.succedent);
}

Sequent apply_KR(Prop A, Sequent sequent){
    // Γ |- Δ から Γ |- Δ, A を導出する
    unordered_set<Prop> new_succedent = sequent.succedent;
    new_succedent.insert(A);
    return Sequent(sequent.antecedent, new_succedent);
}



// ================================================================================================

// プログラム全体をトークナイズする
vector<string> tokenize(string code){
    vector<string> tokens;
    size_t pos = 0;
    for (size_t i = 0; i <= code.size(); i++) {
        // 2文字トークンを優先して切り出す
        if (i + 1 < code.size()) {
            if (code[i] == '|' && code[i + 1] == '-') {
                if (pos < i) {
                    tokens.push_back(code.substr(pos, i - pos));
                }
                tokens.push_back("|-");
                i++;            // '-' をスキップ
                pos = i + 1;     // 次の走査開始位置を更新
                continue;
            }
            if (code[i] == '-' && code[i + 1] == '>') {
                if (pos < i) {
                    tokens.push_back(code.substr(pos, i - pos));
                }
                tokens.push_back("->");
                i++;            // '>' をスキップ
                pos = i + 1;     // 次の走査開始位置を更新
                continue;
            }
        }
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
vector<string> transform_to_RPN(const vector<string>& prop_expression, const set<string>& env_type){
    // Shunting yard algorithm
    stack<string> op_stack;
    vector<string> output_stack;

    for(auto token : prop_expression){
        if (env_type.count(token) != 0) {
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
Prop evaluate_Prop_expression(const vector<string>& prop_expression, const set<string>& env_type){
    vector<string> rpn = transform_to_RPN(prop_expression, env_type);
    if (rpn.empty()) {
        throw runtime_error("Syntax error: invalid expression");
    }
    vector<Prop> prop_stack;
    for (const auto& token : rpn) {
        if (env_type.count(token) != 0) {
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

// 既に定義されているシークエントの識別子が与えられたとき、そのシークエントを返す関数
Sequent read_sequent_identifier(const vector<string>& sequent_tokens, set<string>& env_type, unordered_map<string, Sequent>& env_sequent){
    if (sequent_tokens.size() == 1 && env_sequent.count(sequent_tokens[0]) != 0) {
        return env_sequent[sequent_tokens[0]];
    } else {
        throw runtime_error("Syntax error: expected sequent identifier or sequent expression\n");
    }
}

// シークエントを表すトークン列を受け取って、Sequentオブジェクトを返す関数
Sequent parse_sequent(const vector<string>& sequent_tokens, set<string>& env_type, unordered_map<string, Sequent>& env_sequent){

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
        antecedent.insert(evaluate_Prop_expression(prop, env_type));
    }

    unordered_set<Prop> succedent;
    for (const auto& prop : split(succedent_tokens, ",")) {
        succedent.insert(evaluate_Prop_expression(prop, env_type));
    }

    return Sequent(antecedent, succedent);
}

// 証明の式を評価する関数
Sequent evaluate_proof_expression(const vector<string>& proof_expression, set<string>& env_type, unordered_map<string, Sequent>& env_sequent){
    int N = proof_expression.size();

    int pos = 0;
    vector<string> proof_stack;
    int height = 0;
    vector<int> height_stack;
    while (pos < N) {
        string token = proof_expression[pos];
        proof_stack.push_back(token);
        // それが関数実行の ")" なのか、Prop式の中の")"なのかを見分ける必要がある。
        // 関数実行の開き括弧は ">(" になっているはずなので、">("で開かれた括弧の深さ(height)を保存しておき、
        // その深さを閉じる ")" が来たときだけ関数適用を行う。
        if (token == "(") {
            height++;
            if (proof_stack.size() >= 2 && proof_stack[proof_stack.size() - 2] == ">") {
                height_stack.push_back(height);
            }
        }

        if (token == ")") {
            // まずは括弧の深さを見て「関数引数の閉じ括弧」かどうか判定する。
            if (height_stack.empty() || height_stack.back() != height) {
                height--; // Prop式など、関数呼び出し以外の括弧を閉じる
                pos++;
                continue;
            }
            height_stack.pop_back();

            // 対応する"(" とか "," が出てくるまでスタックからトークンを取り出す
            vector<Sequent> args; // 関数の引数のリスト
            vector<string> current_arg; // 現在処理中の引数
            int paren_count = 1; // "(" と ")" の対応を取るためのカウンタ
            proof_stack.pop_back();
            if((!proof_stack.empty()) && proof_stack.back() == "("){ // 0引数関数の処理
                proof_stack.pop_back();
            } else { 
                while (paren_count > 0) {
                    token = proof_stack.back();
                    proof_stack.pop_back();
                    if (token == "(") {
                        paren_count--;
                    } else if (token == ")") {
                        paren_count++;
                    } else if (token == ",") {
                        if (paren_count == 1) {
                            reverse(current_arg.begin(), current_arg.end());
                            args.push_back(read_sequent_identifier(current_arg, env_type, env_sequent));
                            current_arg.clear();
                        } else {
                            throw runtime_error("Syntax error: unexpected ',' in proof expression");
                        }
                    }
                    if (paren_count > 0 && token != ",") {
                        current_arg.push_back(token);
                    } else if (paren_count == 0) {
                        reverse(current_arg.begin(), current_arg.end());
                        args.push_back(read_sequent_identifier(current_arg, env_type, env_sequent));
                        current_arg.clear();
                        break;
                    }
                }
            }
            reverse(args.begin(), args.end());

            // 同様の処理を、<,>で行う

            // 最初は>が来る
            if (proof_stack.empty() || proof_stack.back() != ">") {
                throw runtime_error("Syntax error: expected '>' in proof expression");
            }
            proof_stack.pop_back();

            vector<Prop> template_args; // 関数のテンプレート引数のリスト
            vector<string> current_template_arg; // 現在処理中のテンプレート引数

            while (!proof_stack.empty()) {
                string token = proof_stack.back();
                proof_stack.pop_back();
                if (token == "<") {
                    reverse(current_template_arg.begin(), current_template_arg.end());
                    template_args.push_back(evaluate_Prop_expression(current_template_arg, env_type));
                    current_template_arg.clear();
                    break;
                } else if (token == ",") {
                    reverse(current_template_arg.begin(), current_template_arg.end());
                    template_args.push_back(evaluate_Prop_expression(current_template_arg, env_type));
                    current_template_arg.clear();
                } else {
                    current_template_arg.push_back(token);
                }
            }
            reverse(template_args.begin(), template_args.end());

            // この後は推論規則(に対応する関数)が来る
            if (proof_stack.empty()) {
                throw runtime_error("Syntax error: expected inference rule in proof expression");
            }
            string inference_rule = proof_stack.back();
            proof_stack.pop_back();
            if (inference_rules.count(inference_rule) == 0) {
                throw runtime_error("Syntax error: unknown inference rule '" + inference_rule + "' in proof expression");
            }

            if (inference_rule_arity[inference_rule] != args.size()) {
                throw runtime_error("Syntax error: incorrect number of arguments for inference rule '" + inference_rule + "' in proof expression");
            }

            if (inference_rule_template_arity[inference_rule] != template_args.size()) {
                throw runtime_error("Syntax error: incorrect number of template arguments for inference rule '" + inference_rule + "' in proof expression");
            }

            Sequent result;
            if (inference_rule == "Id") {
                result = apply_Id(template_args[0]);
            } else if (inference_rule == "andL") {
                result = apply_andL(template_args[0], template_args[1], args[0]);
            } else if (inference_rule == "andR") {
                result = apply_andR(template_args[0], template_args[1], args[0], args[1]);
            } else if (inference_rule == "orL") {
                result = apply_orL(template_args[0], template_args[1], args[0], args[1]);
            } else if (inference_rule == "orR") {
                result = apply_orR(template_args[0], template_args[1], args[0]);
            } else if (inference_rule == "andR") {
                result = apply_andR(template_args[0], template_args[1], args[0], args[1]);
            } else if (inference_rule == "orL") {
                result = apply_orL(template_args[0], template_args[1], args[0], args[1]);
            } else if (inference_rule == "orR") {
                result = apply_orR(template_args[0], template_args[1], args[0]);
            } else if (inference_rule == "impL") {
                result = apply_impL(template_args[0], template_args[1], args[0], args[1]);
            } else if (inference_rule == "impR") {
                result = apply_impR(template_args[0], template_args[1], args[0]);
            } else if (inference_rule == "notL") {
                result = apply_notL(template_args[0], args[0]);
            } else if (inference_rule == "notR") {
                result = apply_notR(template_args[0], args[0]);
            } else if (inference_rule == "KL") {
                result = apply_KL(template_args[0], args[0]);
            } else if (inference_rule == "KR") {
                result = apply_KR(template_args[0], args[0]);
            } else {
                throw runtime_error("Internal error: unhandled inference rule '" + inference_rule + "' in proof expression");
            }

            // 内部的に、_から始まる変数を定義して、resultの値を代入する
            string var_name = get_unique_var_name();
            env_sequent[var_name] = result;
            proof_stack.push_back(var_name);

            // 関数引数の閉じ括弧 ")" を処理したので深さを下げる
            height--;
            
            
        }
        pos++;
    }
    // stackの最後には、シークエントを表す変数名が残っているはずなので、それを返す
    if (proof_stack.size() != 1) {
        throw runtime_error("Syntax error: invalid proof expression");
    }
    string result_var = proof_stack.back();
    if (env_sequent.count(result_var) == 0) {
        throw runtime_error("Syntax error: undefined variable '" + result_var + "' in proof expression");
    }
    return env_sequent[result_var];
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
void match_proof_statement(const vector<string>& tokens, int& pos, set<string>& env_type, unordered_map<string, Sequent>& env_sequent){
    int N = tokens.size();
    // 構文は `[シークエント] 変数名 = 証明のコード` とする

    // [ から始まる
    if (tokens[pos] != "[") {
        throw runtime_error("Syntax error: expected '[' at the beginning of proof declaration\n");
    }
    pos++;  // [をスキップ

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
    if (env_sequent.count(argument_name) != 0){
        throw runtime_error("Syntax error: duplicate declaration of argument '" + argument_name + "'\n");
    }

    // = が来る
    pos++;
    if (pos >= N || tokens[pos] != "="){
        throw runtime_error("Syntax error: expected '=' after argument name in proof declaration\n");
    }

    pos++;  // "=" をスキップ

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

    Sequent result = evaluate_proof_expression(proof_stack, env_type, env_sequent);
    Sequent expected = parse_sequent(sequent_tokens, env_type, env_sequent);
    if (result != expected){
        throw runtime_error("Syntax error: proof expression does not match the expected sequent\n");
    }

    env_sequent.emplace(argument_name, result); // シークエントをパースして、環境に追加する
}

// autoの推論規則を処理する関数
void match_auto_statement(const vector<string>& tokens, int& pos, set<string>& env_type, unordered_map<string, Sequent>& env_sequent){
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
    if (env_sequent.count(argument_name) != 0){
        throw runtime_error("Syntax error: duplicate declaration of argument '" + argument_name + "'\n");
    }

    // = が来る
    pos++;
    if (pos >= N || tokens[pos] != "="){
        throw runtime_error("Syntax error: expected '=' after argument name in proof declaration\n");
    }
    pos++;  //=のスキップ

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
    Sequent result = evaluate_proof_expression(proof_stack, env_type, env_sequent);

    env_sequent.emplace(argument_name, result); // シークエントをパースして、環境に追加する
}

// print文を処理する関数
void match_print_statement(const vector<string>& tokens, int& pos, set<string>& env_type, unordered_map<string, Sequent>& env_sequent){
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

    if (env_sequent.count(argument_name) == 0) {
        throw runtime_error("Syntax error: undefined proof variable '" + argument_name + "' in print statement\n");
    }

    cout << "Proved : " << env_sequent[argument_name].to_string() << endl;
}


// =======================================================================================

string code = "Type A; auto x = Id<A>();";

vector<string> tokens = {"Type", "A", ";", "auto","x","=","Id","<","A",">","()"};

// <code> = [<state>;]*

struct ASTNode{
    string NodeType;
    vector<ASTNode*> children;
};

/*
<code> ::= <state> ";"
<state> ::= Type <id>; | auto <id> = <expr>; | print <id>; | [<seq>] <id> = <expr>;
<seq> ::= <propargs> |- <propargs>
<propargs> ::= <prop> | <prop> "," <propargs> | ε

// <prop> は命題式の解析

<expr> ::= <inference_rule><<propargs>>(<exprargs>);
<inference_rule> ::= Id | andL | andR | orL | orR | impL | impR | notL | notR | KL | KR                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                
<exprargs> ::= <expr> | <expr> "," <exprargs> | ε                          






*/

class Parser {
    const vector<string>& tokens;
    int pos;
    set<string>& env_type;
    unordered_map<string, Sequent>& env_sequent;

    // --- ヘルパー関数 ---
    string peek(int offset = 0) const {
        if (pos + offset < tokens.size()) return tokens[pos + offset];
        return "";
    }

    string advance() {
        if (pos < tokens.size()) return tokens[pos++];
        return "";
    }

    void expect(const string& expected) {
        if (peek() == expected) {
            advance();
        } else {
            throw runtime_error("Syntax error: expected '" + expected + "', but got '" + peek() + "'");
        }
    }

    bool is_inference_rule(const string& name) const {
        return inference_rules.count(name) != 0;
    }

public:
    Parser(const vector<string>& tokens, set<string>& env_type, unordered_map<string, Sequent>& env_sequent)
        : tokens(tokens), pos(0), env_type(env_type), env_sequent(env_sequent) {}

    void parse_program() {
        while (pos < tokens.size()) {
            parse_statement();
        }
    }

private:
    // --- 文 (Statement) のパース ---
    void parse_statement() {
        string t = peek();
        if (t == "Type") parse_type_decl();
        else if (t == "auto") parse_auto_decl();
        else if (t == "[") parse_proof_decl();
        else if (t == "print") parse_print_stmt();
        else if (t == ";") advance(); // 空文のスキップ
        else throw runtime_error("Syntax error: unexpected token '" + t + "' at statement level");
    }

    void parse_type_decl() {
        expect("Type");
        string name = advance();
        if (!validate_var(name)) throw runtime_error("Syntax error: invalid Type name '" + name + "'");
        if (env_type.count(name)) throw runtime_error("Syntax error: Type '" + name + "' already defined");
        env_type.insert(name);
        expect(";");
    }

    void parse_auto_decl() {
        expect("auto");
        string name = advance();
        if (!validate_var(name)) throw runtime_error("Syntax error: invalid variable name '" + name + "'");
        expect("=");
        Sequent seq = parse_expr();
        env_sequent[name] = seq;
        expect(";");
    }

    void parse_proof_decl() {
        expect("[");
        Sequent expected_seq = parse_sequent();
        expect("]");
        
        string name = advance();
        if (!validate_var(name)) throw runtime_error("Syntax error: invalid variable name '" + name + "'");
        
        expect("=");
        Sequent result_seq = parse_expr();
        expect(";");

        if (expected_seq != result_seq) {
            throw runtime_error("Type error: proof expression does not match the declared sequent for '" + name + "'");
        }
        env_sequent[name] = result_seq;
    }

    void parse_print_stmt() {
        expect("print");
        string name = advance();
        expect(";");
        if (env_sequent.count(name) == 0) throw runtime_error("Syntax error: undefined proof variable '" + name + "'");
        cout << "Proved : " << env_sequent[name].to_string() << "\n";
    }

    // --- シークエントのパース ---
    Sequent parse_sequent() {
        unordered_set<Prop> antecedent;
        if (peek() != "|-") {
            antecedent = parse_prop_list();
        }
        expect("|-");
        unordered_set<Prop> succedent;
        if (peek() != "]") { // proof_decl内での呼び出しを想定
            succedent = parse_prop_list();
        }
        return Sequent(antecedent, succedent);
    }

    unordered_set<Prop> parse_prop_list() {
        unordered_set<Prop> props;
        props.insert(parse_prop());
        while (peek() == ",") {
            advance();
            props.insert(parse_prop());
        }
        return props;
    }

    // --- 証明式 (Expr) のパース ---
    Sequent parse_expr() {
        // LL(2) 先読み: 識別子の次が '<' なら推論規則
        if (is_inference_rule(peek()) && peek(1) == "<") {
            string rule = advance();
            expect("<");
            
            vector<Prop> template_args;
            if (peek() != ">") {
                template_args.push_back(parse_prop());
                while (peek() == ",") {
                    advance();
                    template_args.push_back(parse_prop());
                }
            }
            expect(">");
            expect("(");
            
            vector<Sequent> args;
            if (peek() != ")") {
                args.push_back(parse_expr());
                while (peek() == ",") {
                    advance();
                    args.push_back(parse_expr());
                }
            }
            expect(")");

            // Arity check
            if (inference_rule_template_arity[rule] != template_args.size()) {
                throw runtime_error("Syntax error: incorrect template arguments for '" + rule + "'");
            }
            if (inference_rule_arity[rule] != args.size()) {
                throw runtime_error("Syntax error: incorrect arguments for '" + rule + "'");
            }

            // Apply rule (既存の関数を呼び出す)
            if (rule == "Id") return apply_Id(template_args[0]);
            if (rule == "andL") return apply_andL(template_args[0], template_args[1], args[0]);
            if (rule == "andR") return apply_andR(template_args[0], template_args[1], args[0], args[1]);
            if (rule == "orL") return apply_orL(template_args[0], template_args[1], args[0], args[1]);
            if (rule == "orR") return apply_orR(template_args[0], template_args[1], args[0]);
            if (rule == "impL") return apply_impL(template_args[0], template_args[1], args[0], args[1]);
            if (rule == "impR") return apply_impR(template_args[0], template_args[1], args[0]);
            if (rule == "notL") return apply_notL(template_args[0], args[0]);
            if (rule == "notR") return apply_notR(template_args[0], args[0]);
            if (rule == "KL") return apply_KL(template_args[0], args[0]);
            if (rule == "KR") return apply_KR(template_args[0], args[0]);
            
            throw runtime_error("Internal error: unhandled rule " + rule);
        } else {
            // 変数としてのパース
            string name = advance();
            if (env_sequent.count(name) == 0) {
                throw runtime_error("Syntax error: undefined proof variable '" + name + "'");
            }
            return env_sequent[name];
        }
    }

    // --- 命題論理式 (Prop) のパース ---
    Prop parse_prop() {
        return parse_imp_expr();
    }

    // -> は右結合 (A -> B -> C は A -> (B -> C))
    Prop parse_imp_expr() {
        Prop left = parse_or_expr();
        if (peek() == "->") {
            advance();
            Prop right = parse_imp_expr(); // 右側は再帰呼び出し
            return PropImp(left, right);
        }
        return left;
    }

    // + は左結合 (A + B + C は (A + B) + C)
    Prop parse_or_expr() {
        Prop left = parse_and_expr();
        while (peek() == "+") {
            advance();
            Prop right = parse_and_expr();
            left = PropOr(left, right); // ループで左から包んでいく
        }
        return left;
    }

    // * は左結合
    Prop parse_and_expr() {
        Prop left = parse_unary_expr();
        while (peek() == "*") {
            advance();
            Prop right = parse_unary_expr();
            left = PropAnd(left, right);
        }
        return left;
    }

    // ~ は右結合 (~~A は ~(~A))
    Prop parse_unary_expr() {
        if (peek() == "~") {
            advance();
            return PropNot(parse_unary_expr());
        }
        return parse_primary_prop();
    }

    Prop parse_primary_prop() {
        string t = peek();
        if (t == "(") {
            advance();
            Prop p = parse_prop();
            expect(")");
            return p;
        } else {
            advance();
            if (env_type.count(t) == 0) {
                throw runtime_error("Type error: undefined Type variable '" + t + "'");
            }
            return PropVar(t);
        }
    }
};

// --- main.cpp 内の compile 関数の置き換え ---
int compile(const string& code) {
    vector<string> tokens = tokenize(code);
    set<string> env_type;
    unordered_map<string, Sequent> env_sequent;

    Parser parser(tokens, env_type, env_sequent);
    parser.parse_program();

    return 0;
}


// ===============================================================================

int main(){
    ios::sync_with_stdio(false);
    std::cin.tie(nullptr);
    
}