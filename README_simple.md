# ProofAssistant クイックリファレンス

## ビルド

```bash
make
```

または：

```bash
g++ -std=c++23 -O2 main3.cpp -o main3
```

## 証明を検査

```bash
./main3 proofs/iff.n3
```

Ramseyの証明：

```bash
./main3 "proofs/Ramsey's_theorem.n3"
```

成功時の終了コードは`0`です。

## 自動証明を生成

```bash
python3 main.py "|- A->A" -o /tmp/proof.n3
./main3 /tmp/proof.n3
```

モーダスポネンス：

```bash
python3 main.py "A,A->B |- B" -o /tmp/modus_ponens.n3
```

Ramsey上下界を再生成：

```bash
python3 demos/generate_ramsey_proof.py
```

## LaTeX証明図

標準出力：

```bash
./main3 --latex demos/02_modus_ponens.n3
```

ファイルへ保存：

```bash
./main3 --latex demos/02_modus_ponens.n3 -o proof.tex
pdflatex proof.tex
```

## VS Code / LSP

```bash
make extension-install
```

その後、VS Codeで`Developer: Reload Window`を実行します。

利用できる機能：

- 編集中のDiagnostic
- Hover
- 識別子・対応括弧のハイライト
- Semantic Tokens
- `Type`、`auto`、`print`、推論規則名の補完

## テスト

```bash
make test
```

## `.n3`の基本構文

```n3
// comment
Type A;
Type B;

auto identity = Id<A>();

[A,A->B |- B] modus_ponens =
    impL<A,B>(
        KR<B>(Id<A>()),
        KL<A>(Id<B>())
    );

print modus_ponens;
```

命題演算子：

```text
~A       否定
A*B      連言
A+B      選言
A->B     含意
```

優先順位：

```text
~ > * > + > ->
```

推論規則：

```text
Id
KL  KR
notL notR
andL andR
orL  orR
impL impR
cut
```

空文`;`と`//`行コメントを使用できます。
