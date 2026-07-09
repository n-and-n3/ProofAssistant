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
            if (i < code.size() && Syntax_Symbols.contains(string(1, code[i]))) {
                tokens.push_back(string(1, code[i]));
            }
            pos = i + 1;
        }
    }
    return tokens;
}



// =======================================================================================


struct ASTNode{
    string NodeType;
    vector<ASTNode*> children;

    ASTNode(string _nodetype, vector<ASTNode*> _children = {}) : NodeType(_nodetype), children(_children) {}  
};


ASTNode* parse_identifier(const vector<string> &tokens, int &pc){
    assert(pc < ssize(tokens));
    if (!keywords.contains(tokens[pc]) && !Syntax_Symbols.contains(tokens[pc])){
        ASTNode* node = new ASTNode("identifier", {});
        pc += 1;
        return node;
    } else {
        throw runtime_error("error\n");
    }
}

ASTNode* parse_expression(const vector<string> &tokens, int &pc){
    // 関数式を解析する
    assert(pc < ssize(tokens));
    // WIP
    // 関数一覧の要素 <型, 型, ...>(命題, 命題, ...)
    if (inference_rules.contains(tokens[pc])){
        string rule_name = tokens[pc];
        pc += 1;
        assert(pc < ssize(tokens) && tokens[pc] == "<");
        pc += 1;
        vector<ASTNode*> type_args;
        rep(_, inference_rule_template_arity[rule_name]){
            type_args.push_back(parse_identifier(tokens, pc));
            if (pc < ssize(tokens) && tokens[pc] == ","){
                pc += 1; // skip ','
            }
        }
        assert(pc < ssize(tokens) && tokens[pc] == ">");
        pc += 1; // skip '>'
        assert(pc < ssize(tokens) && tokens[pc] == "(");
        pc += 1; // skip '('
        vector<ASTNode*> prop_args;
        rep(_, inference_rule_arity[rule_name]){
            prop_args.push_back(parse_expression(tokens, pc));
            if (pc < ssize(tokens) && tokens[pc] == ","){
                pc += 1; // skip ','
            }
        }
        assert(pc < ssize(tokens) && tokens[pc] == ")");
        pc += 1; // skip ')'
        ASTNode* node = new ASTNode("function", {new ASTNode(rule_name, type_args), new ASTNode("args", prop_args)});
        return node;
    }
    return nullptr;
}


ASTNode* parse_factor(const vector<string> &tokens, int &pc){
    // parse_factor
    assert(pc < ssize(tokens));
    if (tokens[pc] == "("){
        pc += 1;
        auto tmp = parse_expression(tokens, pc);
        assert(pc < ssize(tokens) && tokens[pc] == ")");
        pc += 1;
        return tmp;
    } else {
        return parse_identifier(tokens, pc);
    }
}

ASTNode* parse_not(const vector<string> &tokens, int &pc){
    // ~ parse_factor
    assert(pc < ssize(tokens));
    if (tokens[pc] == "~"){
        pc += 1;
        auto tmp = parse_not(tokens, pc);
        return new ASTNode("not", {tmp});
    } else {
        auto tmp = parse_factor(tokens, pc);
        return tmp;
    }
}


ASTNode* parse_and(const vector<string> &tokens, int &pc){
    // parse_not * parse_and
    assert(pc < ssize(tokens));
    ASTNode* left = parse_not(tokens, pc);
    while (pc < ssize(tokens) && tokens[pc] == "*"){
        pc += 1;
        auto right = parse_not(tokens, pc);
        left = new ASTNode("and", {left, right});
    }
    return left;
}


ASTNode* parse_or(const vector<string> &tokens, int &pc){
    // parse_or + parse_and
    assert(pc < ssize(tokens));
    ASTNode* left = parse_and(tokens, pc);
    while (pc < ssize(tokens) && tokens[pc] == "+"){
        pc += 1;
        auto right = parse_and(tokens, pc);
        left = new ASTNode("or", {left, right});
    }
    return left;
}


ASTNode* parse_imp(const vector<string> &tokens, int &pc){
    // parse_or -> parse_imp
    assert(pc < ssize(tokens));
    auto left = parse_or(tokens, pc);
    if (pc < ssize(tokens) && tokens[pc] == "->"){
        pc += 1;
        auto right = parse_imp(tokens, pc);
        return new ASTNode("imp", {left, right});
    }
    return left;
}

ASTNode* parse_prop(const vector<string> &tokens, int &pc){
    // parse_imp
    assert(pc < ssize(tokens));
    return parse_imp(tokens, pc);
}


ASTNode* parse_propargs(const vector<string> &tokens, int &pc){
    // prop, prop, ...
    assert(pc < ssize(tokens));
    ASTNode* main = new ASTNode("code",{});
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

ASTNode* parse_sequent(const vector<string> &tokens, int &pc){
    // propargs |- propargs
    assert(pc < ssize(tokens));
    auto tmp1 = parse_propargs(tokens, pc);
    assert(pc < ssize(tokens) && tokens[pc] == "|-");
    pc += 1;
    auto tmp2 = parse_propargs(tokens, pc);
    ASTNode* node = new ASTNode("sequent", {tmp1, tmp2});
    return node;
}

ASTNode* parse_code(const vector<string> &tokens, int &pc){
    ASTNode* main = new ASTNode("code",{});
    while (pc < ssize(tokens)){
        string key = tokens[pc];
        if (key == ";"){
            pc += 1;
            return parse_code(tokens, pc);
        } else {
            if (key == "print"){
                // print identifier;
                pc += 1;
                auto tmp = parse_identifier(tokens, pc);
                ASTNode* state = new ASTNode("print",{tmp});
                main->children.push_back(state);
                assert(pc < ssize(tokens) && tokens[pc] == ";");
                pc += 1;
            } else if (key == "Type"){
                // Type identifier;
                pc += 1;
                auto tmp = parse_identifier(tokens, pc);
                ASTNode* state = new ASTNode("Type", {tmp});
                main->children.push_back(state);
                assert(pc < ssize(tokens) && tokens[pc] == ";");
                pc += 1;
            } else if (key == "auto"){
                // auto identifier = expression;
                pc += 1;
                auto tmp1 = parse_identifier(tokens, pc);
                assert(pc < ssize(tokens) && tokens[pc] == "=");
                pc += 1;
                auto tmp2 = parse_expression(tokens, pc);
                ASTNode* state = new ASTNode("auto", {tmp1, tmp2});
                main->children.push_back(state);
                assert(pc < ssize(tokens) && tokens[pc] == ";");
                pc += 1;
            } else if (key == "["){
                // [sequent] identifier = expression;
                pc += 1;
                auto tmp1 = parse_sequent(tokens, pc);
                assert(pc < ssize(tokens) && tokens[pc] == "]");
                pc += 1;
                auto tmp2 = parse_identifier(tokens, pc);
                assert(pc < ssize(tokens) && tokens[pc] == "=");
                pc += 1;
                auto tmp3 = parse_expression(tokens, pc);
                ASTNode* state = new ASTNode("var", {tmp1, tmp2, tmp3});
                main->children.push_back(state);
                assert(pc < ssize(tokens) && tokens[pc] == ";");
                pc += 1;
            } else {
                throw runtime_error("error\n");
            }
        }
    }


    // EoF
    if (pc == ssize(tokens)){
        return nullptr;
    } else {
        throw runtime_error("error\n");
    }

    return main;
}

void print_ast(ASTNode* node, int depth = 0) {
    if (!node) return;
    cout << string(depth * 2, ' ') << node->NodeType << "\n";
    for (auto child : node->children) {
        print_ast(child, depth + 1);
    }
}

ASTNode* parser(const vector<string>& tokens){
    int pc = 0;
    return parse_code(tokens, pc);
}


int compile(const string& code) {
    vector<string> tokens = tokenize(code);
    vout(tokens);

    ASTNode* root = parser(tokens);

    print_ast(root);

    return 0;
}


// ===============================================================================

int main(){
    ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    string code = "Type A; auto x = Id<A>();";
    int result = compile(code);
    cout << result << "\n";
}