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

set<string> Inference_Rules = {
    "Iand", "Eland", "Erand", "Ilor", "Iror", "Eor", "Iimp", "Eimp"
};

set<string> Curry_Rules = {
    "Curryr", "Curryl"
};

set<string> Logical_Connectives = {
    "*", "+", "->"
};

set<string> keywords = {
    "Prop", "proof"
};

set<string> Syntax_Symbols = {
    "(", ")", "{", "}", ";", ",", ":", "*", "+", "-", "<", ">", ";"
};


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

bool check_type(vector<string>& expression_arg_stack, vector<string>& expression_ret_stack, vector<string>& proof_tokens, set<string>& env, string& argument_name){
    // ここで proof_tokens を解析して、型チェックを行う
    // expression_arg_stack は proof の引数のスタック、expression_ret_stack は式のスタック、env は型環境
    // argument_name は proof の引数の名前

    // 例えば、proof_tokens を左から順に見ていって、Inference_Rules や Curry_Rules が出てきたらスタックから必要な数だけ取り出して型をチェックする、など
    // 成功したら true を返す, 失敗したら false を返す

    // 解析結果のprint
    for (const auto& token : expression_arg_stack) {
        cout << "Expression Arg Stack: " << token << "\n";
    }
    for (const auto& token : expression_ret_stack) {
        cout << "Expression Ret Stack: " << token << "\n";
    }
    for (const auto& token : proof_tokens) {
        cout << "Proof Token: " << token << "\n";
    }
    for (const auto& token : env) {
        cout << "Environment Token: " << token << "\n";
    }
    cout << "Argument Name: " << argument_name << "\n";

    return true; // 仮に常に成功するようにしておく
}

int compile(string code){
    vector<string> tokens = tokenize(code);
    // ここでトークンを解析して、型チェックや証明の検証を行う
    // 例えば、トークンをスタックに積んでいって、演算子が出てきたらスタックから必要な数だけ取り出して型をチェックする、など
    // 成功したら0を返す, 失敗したらエラーコードを返す

    set<string> env; // 型環境
    vector<string> expression_ret_stack; // 式のスタック、型を表す文字列を積む

    for (int i = 0; i < tokens.size(); i++) {
        string token = tokens[i];
        if (keywords.count(token)) {
            if (token == "Prop") {
                env.insert(tokens[i + 1]); // 次のトークンは型の名前
                i++; // 次のトークンはスキップ
            } else if (token == "proof") {
                // 波括弧の中のコードを取得して check_type 関数に渡す
                // 型 proof(変数名:型){証明} の形式で書かれている
                vector<string> expression_arg_stack;
                vector<string> proof_tokens;
                string argument_name;
                // ここで proof の引数と証明のコードを解析して、expression_arg_stack と proof_tokens に格納する
                // まずは　proof の引数を解析する
                if (tokens[i + 1] != "(") {
                    cout << "Syntax error: expected '(' after 'proof'\n";
                    return -1; // syntax error
                }
                i += 2; // "proof" と "(" をスキップ

                argument_name = tokens[i]; // 変数名
                i++; // 変数名をスキップ
                if (tokens[i] != ":") {
                    cout << "Syntax error: expected ':' after proof argument name\n";
                    return -1; // syntax error
                }
                i++; // ":" をスキップ

                // ここは、()の対応を取る必要がある
                int paren_count = 1; // "(" はすでに1つ見ている
                while (i < tokens.size() && paren_count > 0) {
                    if (tokens[i] == "(") {
                        paren_count++;
                    } else if (tokens[i] == ")") {
                        paren_count--;
                    }
                    if (paren_count > 0) { // 対応する ")" を見つけるまでは引数スタックに入れる
                        expression_arg_stack.push_back(tokens[i]);
                    }
                    i++;
                }

                // proof の本体を解析する
                if (i >= tokens.size() || tokens[i] != "{") {
                    cout << "Syntax error: expected '{' after proof arguments\n";
                    return -1; // syntax error
                }
                i++; // "{" をスキップ
                // while で次の "}"が出てくるまで右に行く
                while (i < tokens.size() && tokens[i] != "}") {
                    proof_tokens.push_back(tokens[i]);
                    i++;
                }
                if (i >= tokens.size() || tokens[i] != "}") {
                    cout << "Syntax error: expected '}' at the end of proof\n";
                    return -1; // syntax error
                }

                bool result = check_type(expression_arg_stack, expression_ret_stack, proof_tokens, env, argument_name);

                if (!result) {
                    cout << "Type check failed for proof: " << argument_name << "\n";
                    return -1; // type check failed
                } else {
                    // type check succeeded, continue parsing the rest of the code
                    return 0;
                }

            }
        } else if (Inference_Rules.count(token) || Curry_Rules.count(token) || Logical_Connectives.count(token) || env.count(token)) {
            expression_ret_stack.push_back(token);
        } else if (token == ";") {
            expression_ret_stack.clear(); // セミコロンで式のスタックをクリアする
        } else {
            cout << "Unknown token: " << token << "\n";
            return -1; // 不明なトークン
        }
    }
    return 0; // ここを通るということは、証明を検証するコードがなかったということなので、まあ成功とみなす
}


int main(){
    ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    // ========= Write your code here! ============================================================================
    //                                       
    string code = "Prop P;\nProp Q;\nProp R;\n\nP*Q + P*R proof(h : P * (Q + R)){\nEor(Erand(h), Curryr<Q>(Ilor<P*R>(Iand), Eland(h)), Curryr<R>(Iror<P*Q>(Iand), Eland(h)))\n}";
    //                                    
    // ============================================================================================================


    vector<string> tokens = tokenize(code);

    for (const auto& token : tokens) {
        if (keywords.count(token)) {
            cout << "Keyword: " << token << "\n";
        } else if (Inference_Rules.count(token)) {
            cout << "Inference Rule: " << token << "\n";
        } else if (Curry_Rules.count(token)) {
            cout << "Curry Rule: " << token << "\n";
        } else if (Logical_Connectives.count(token)) {
            cout << "Logical Connective: " << token << "\n";
        } else {
            cout << "Identifier: " << token << "\n";
        }
    }

    int result = compile(code);
    if (result == 0) {
        cout << "Compilation succeeded!\n";
    } else {
        cout << "Compilation failed with error code: " << result << "\n";
    }

}

/*
メタコード
Prop Iand(A : Prop, B : Prop){
  return A * B;
}

Prop Eland(X : Prop * Prop){
  return X.left;
}

Prop Erand(X : Prop * Prop){
  return X.right;
}

Prop Iror<Q : Prop>(P : Prop){
  return P + Q;
}


Prop Iror<Q : Prop>(P : Prop){
  return P + Q;
}

Prop Eor(P : Prop + Prop, f : Prop(Prop), g : Prop(Prop)){
  return f(P.right);
}

Prop Iimp(X : Prop(Prop)){
  return X.domain -> Y.codomain;
}
  
Prop Iimp(X : Prop(Prop)){
  return X.domain -> Y.codomain;
}

Prop Eimp(X : Prop -> Prop, Y : Prop){
  return X(Y);
}

Prop(Prop) Curryr< : Prop>(f : Prop(Prop, Prop),Y : Prop){
  return lambda x: Curryl(x, Y)
}

Prop(Prop) Curryl< : Prop>(f : Prop(Prop, Prop),X : Prop){
  return lambda y: Curryl(X, y)
}

// 否定の導入、除去、背理法は後でやる

*/

// $$ P \land (Q \lor R) \implies (P \land Q) \lor (P \land R) $$

/*
Prop P;
Prop Q;
Prop R;

P*Q + P*R proof(h : P * (Q + R)){
  Eor(Erand(h), Curryr<Q>(Ilor<P*R>(Iand), Eland(h)), Curryr<R>(Iror<P*Q>(Iand), Eland(h)));
}
*/
