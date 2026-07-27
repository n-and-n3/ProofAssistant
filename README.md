# ProofAssistant

命題論理のシークエント計算（LK）を、推論規則の合成として記述・検証する
ミニ証明言語です。ソースファイルには`.n3`拡張子を使用します。

主な機能は次のとおりです。

- C++カーネルによる証明検査
- 構文・未定義変数・型・推論規則・証明結果のDiagnostic
- Pythonによる命題論理の自動証明生成
- `bussproofs`を使ったLaTeX証明図出力
- VS Code用LSP
  - 編集中のDiagnostic
  - Hover
  - 同一識別子と対応括弧のハイライト
  - Semantic Tokens
  - 予約語・推論規則の補完
- `//`による行コメント
- 空文`;`
- `cut`規則

## 必要環境

- C++23対応コンパイラ（GCC 13以降を推奨）
- Python 3.10以降
- LSP拡張を使う場合はVS Code
- PDFを作る場合はLaTeX、`bussproofs`、`adjustbox`

## ビルド

```bash
g++ -std=c++23 -O2 -Wall -Wextra main3.cpp -o main3
```

または、

```bash
make
```

警告もエラーとして検査する場合：

```bash
g++ -std=c++23 -O2 -Wall -Wextra -Werror main3.cpp -o main3
```

## 証明を検査する

```bash
./main3 proofs/iff.n3
```

ファイル名に空白や`'`などのシェル記号が含まれる場合は引用符で囲みます。

```bash
./main3 "proofs/Ramsey's_theorem.n3"
```

成功時は`print`されたシークエントと、最後に`0`が表示されます。
失敗時の終了コードは非0です。

```bash
./main3 proofs/iff.n3 >/dev/null
echo $?
```

## `.n3`言語

### 文

すべての文は`;`で終わります。改行は空白として扱われます。

```n3
Type A;
auto identity = Id<A>();
[A |- A] checked_identity = Id<A>();
print checked_identity;
```

- `Type A;`
  - 命題変数を宣言します。
- `auto name = proof;`
  - 証明式を評価し、得られたシークエントへ名前を付けます。
- `[expected] name = proof;`
  - 証明結果が`expected`と一致することも検査します。
- `print name;`
  - 検査成功後、CLI実行時にシークエントを出力します。
- `;`
  - 空文です。複数並べても構いません。

命題変数名とシークエント変数名は同じ名前空間に属し、重複定義できません。

### コメント

`//`から行末まではコメントです。

```n3
// Identity theorem
Type A;
```

### 命題

```n3
A
~A
A*B
A+B
A->B
(A+B)->C
```

優先順位は強い順に次のとおりです。

```text
~  >  *  >  +  >  ->
```

`->`は右結合です。

```text
A->B->C  =  A->(B->C)
```

### シークエント

```n3
A,B |- C
|- A->A
A |-
```

左右の文脈は集合として扱われます。

- 順序は意味に影響しません。
- 同じ命題の重複は除去されます。
- `print`時の表示順は保証されません。

### 証明式

```n3
rule<命題引数...>(前提証明...)
```

例：

```n3
auto identity = Id<A>();
auto weakened = KL<B>(identity);
```

丸括弧内の前提には、先に宣言したシークエント変数を渡します。

## 推論規則

以下で`Γ`と`Δ`はそれぞれ左辺・右辺の共通文脈です。

### 恒等規則

```n3
Id<A>()
```

```text
A |- A
```

### 弱化

```n3
KL<A>(premise)
KR<A>(premise)
```

```text
Γ |- Δ
──────── KL
A,Γ |- Δ

Γ |- Δ
──────── KR
Γ |- Δ,A
```

### 否定

```n3
notL<A>(premise)
notR<A>(premise)
```

```text
Γ |- Δ,A
────────── notL
~A,Γ |- Δ

A,Γ |- Δ
────────── notR
Γ |- Δ,~A
```

### 連言

```n3
andL<A,B>(premise)
andR<A,B>(left_proof, right_proof)
```

```text
A,B,Γ |- Δ
──────────── andL
A*B,Γ |- Δ

Γ |- Δ,A    Γ |- Δ,B
───────────────────── andR
Γ |- Δ,A*B
```

### 選言

```n3
orL<A,B>(left_proof, right_proof)
orR<A,B>(premise)
```

```text
A,Γ |- Δ    B,Γ |- Δ
───────────────────── orL
A+B,Γ |- Δ

Γ |- Δ,A,B
──────────── orR
Γ |- Δ,A+B
```

### 含意

```n3
impL<A,B>(left_proof, right_proof)
impR<A,B>(premise)
```

```text
Γ |- Δ,A    B,Γ |- Δ
───────────────────── impL
A->B,Γ |- Δ

A,Γ |- Δ,B
──────────── impR
Γ |- Δ,A->B
```

### Cut

```n3
cut<A>(left_proof, right_proof)
```

```text
Γ |- Δ,A    A,Γ |- Δ
───────────────────── cut
Γ |- Δ
```

## 短い例

恒等定理：

```n3
Type A;

[|- A->A] identity = impR<A,A>(Id<A>());
print identity;
```

モーダスポネンス：

```n3
Type A;
Type B;

[A,A->B |- B] modus_ponens =
    impL<A,B>(
        KR<B>(Id<A>()),
        KL<A>(Id<B>())
    );

print modus_ponens;
```

そのまま実行できる例は`demos/`と`proofs/`にあります。

## Diagnostic

ユーザーコードに起因する問題は、可能な限り複数まとめて報告されます。

- 文法エラー
- 未定義の命題変数・シークエント変数
- 命題変数とシークエント変数の型不一致
- 重複定義
- 推論規則の引数不足・適用条件違反
- 宣言したシークエントと証明結果の不一致

未知のAST kindや壊れたASTなど、カーネル内部の不整合は内部例外です。

## Python自動証明器

指定した妥当なシークエントから`.n3`証明を生成します。

```bash
python3 main.py "|- A->A"
```

ファイルへ保存：

```bash
python3 main.py "A,A->B |- B" -o /tmp/modus_ponens.n3
./main3 /tmp/modus_ponens.n3
```

シークエントは、シェルの`|`、`>`、`*`から保護するため引用符で囲んで
ください。

証明不能なシークエントでは非0終了します。

```bash
python3 main.py "|- A"
```

ヘルプ：

```bash
python3 main.py --help
```

### Ramseyの専用生成器

`R(3,3) <= 6`と`R(3,3) > 5`の証明を生成します。

```bash
python3 demos/generate_ramsey_proof.py
./main3 "proofs/Ramsey's_theorem.n3"
```

上界証明は、辺の2色を場合分けし、単色三角形が現れた枝を閉じて、
排中律と`cut`で結合します。下界証明は、K5の2つの補な5-cycleを具体的な
彩色として使用します。

## LaTeX証明図

`print`が参照する証明を、単独でコンパイル可能なLaTeX文書へ変換します。

```bash
./main3 --latex demos/02_modus_ponens.n3
```

ファイルへ保存：

```bash
./main3 --latex demos/02_modus_ponens.n3 -o modus_ponens.tex
pdflatex modus_ponens.tex
```

出力は次のパッケージを使用します。

```latex
\usepackage{amsmath}
\usepackage{bussproofs}
\usepackage{adjustbox}
\usepackage[a4paper,landscape,margin=1cm]{geometry}
```

幅の広い証明図はページ幅へ縮小され、複数の`print`は別ページになります。

## VS Code / LSP

LSPは保存前のエディタ内容を全文同期で解析します。差分同期は使用しません。

利用できる機能：

- Diagnostic
- Hover
- 同じ識別子のDocument Highlight
- `()`, `[]`, `{}`, `<>`の字句トークン単位の対応ハイライト
  - `A->B`の`>`は角括弧として数えません。
- Semantic Tokens
- `Type`、`auto`、`print`、推論規則名の補完
  - 変数名やシークエント名は補完しません。

ビルド：

```bash
make lsp
```

現在のローカルまたはVS Code Server環境へインストール：

```bash
make extension-install
```

インストール後、VS Codeで`Developer: Reload Window`を実行し、`.n3`ファイルを
開いてください。

拡張ディレクトリを明示する場合：

```bash
VSCODE_EXTENSIONS_DIR=/path/to/extensions make extension-install
```

LSPサーバーをstdioで直接起動する場合：

```bash
PROOFASSISTANT_ANALYZER="$PWD/vscode-extension/bin/proofassistant" \
python3 lsp/server.py
```

解析器とのJSON境界を確認する場合：

```bash
./main3 --analyze-json < proofs/iff.n3
```

## テスト

```bash
python3 -m unittest tests.test_main tests.test_lsp
```

コンパイラを厳密にビルドし、強い回帰ケースを実行：

```bash
g++ -std=c++23 -O2 -Wall -Wextra -Werror main3.cpp -o /tmp/main3-check
/tmp/main3-check proofs/iff.n3
```

## 実装の分離

- `main2.cpp`
  - Tokenizer、Parser、AST、SymbolTable、Diagnostic、証明カーネル
- `proofassistant.hpp` / `proofassistant.cpp`
  - `analyze()`、`execute()`、`ExecutionResult`、LaTeX出力
- `main3.cpp`
  - CLIと`--analyze-json`
- `main.py`
  - 一般的な命題論理の自動証明器
- `lsp/server.py`
  - 全文同期LSPサーバー
- `vscode-extension/`
  - 依存パッケージなしのVS Codeクライアント

`analyze()`は標準出力へ書き込みません。`execute()`は`print`結果とLaTeXを
`ExecutionResult`として返し、CLIだけが実際の出力を担当します。
