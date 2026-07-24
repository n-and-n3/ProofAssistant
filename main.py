"""README の .n3 形式に対応した命題論理の自動証明生成器。"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from functools import cache
from pathlib import Path
from typing import Iterable, Iterator, Sequence


DEFAULT_SEQUENT = "|- A->A"
RESERVED_IDENTIFIERS = frozenset({"Type", "auto", "print"})
IDENTIFIER_RE = re.compile(r"[A-Za-z][A-Za-z0-9_]*")


class ProofAssistantError(Exception):
    """利用者にそのまま表示できるエラー。"""


class ParseError(ProofAssistantError):
    """入力されたシークエントの構文エラー。"""


class UnprovableError(ProofAssistantError):
    """入力されたシークエントが証明不能であることを表す。"""


class ProofConstructionError(RuntimeError):
    """証明生成器と .n3 カーネルの規則が一致しない内部エラー。"""


@dataclass(frozen=True, slots=True)
class Prop:
    """構造比較・ハッシュ化が可能な命題 AST。"""

    kind: str
    name: str = ""
    args: tuple["Prop", ...] = ()

    @classmethod
    def variable(cls, name: str) -> "Prop":
        return cls("var", name)

    @classmethod
    def unary(cls, kind: str, operand: "Prop") -> "Prop":
        return cls(kind, args=(operand,))

    @classmethod
    def binary(cls, kind: str, left: "Prop", right: "Prop") -> "Prop":
        return cls(kind, args=(left, right))

    def __invert__(self) -> "Prop":
        return Prop.unary("not", self)

    def __mul__(self, other: "Prop") -> "Prop":
        return Prop.binary("and", self, other)

    def __add__(self, other: "Prop") -> "Prop":
        return Prop.binary("or", self, other)

    def __rshift__(self, other: "Prop") -> "Prop":
        return Prop.binary("imp", self, other)

    def __str__(self) -> str:
        return format_prop(self)


@dataclass(frozen=True, slots=True, init=False)
class Sequent:
    """README と C++ 実装に合わせ、左右の文脈を集合として保持する。"""

    antecedent: frozenset[Prop]
    succedent: frozenset[Prop]

    def __init__(
        self,
        antecedent: Iterable[Prop] = (),
        succedent: Iterable[Prop] = (),
    ) -> None:
        object.__setattr__(self, "antecedent", frozenset(antecedent))
        object.__setattr__(self, "succedent", frozenset(succedent))

    @property
    def ant(self) -> frozenset[Prop]:
        return self.antecedent

    @property
    def suc(self) -> frozenset[Prop]:
        return self.succedent

    def __str__(self) -> str:
        return format_sequent(self)


@dataclass(frozen=True, slots=True)
class Proof:
    """1つの推論規則と、その前提・結論からなる証明木。"""

    rule: str
    template_args: tuple[Prop, ...]
    premises: tuple["Proof", ...]
    conclusion: Sequent


@dataclass(frozen=True, slots=True)
class Token:
    value: str
    offset: int


def tokenize(text: str) -> tuple[Token, ...]:
    tokens: list[Token] = []
    index = 0
    while index < len(text):
        if text[index].isspace():
            index += 1
            continue
        if text.startswith("|-", index) or text.startswith("->", index):
            tokens.append(Token(text[index : index + 2], index))
            index += 2
            continue
        if text[index] in "(),*+~":
            tokens.append(Token(text[index], index))
            index += 1
            continue
        match = IDENTIFIER_RE.match(text, index)
        if match is not None:
            tokens.append(Token(match.group(0), index))
            index = match.end()
            continue
        raise ParseError(
            f"構文エラー（位置 {index + 1}）: "
            f"使用できない文字 {text[index]!r} があります"
        )
    return tuple(tokens)


class Parser:
    def __init__(self, text: str):
        self.text = text
        self.tokens = tokenize(text)
        self.position = 0

    def peek(self) -> Token | None:
        if self.position == len(self.tokens):
            return None
        return self.tokens[self.position]

    def accept(self, value: str) -> bool:
        token = self.peek()
        if token is None or token.value != value:
            return False
        self.position += 1
        return True

    def expect(self, value: str) -> Token:
        token = self.peek()
        if token is None:
            raise self.error(f"{value!r} が必要ですが、入力が終わりました")
        if token.value != value:
            raise self.error(
                f"{value!r} が必要ですが、{token.value!r} が見つかりました",
                token,
            )
        self.position += 1
        return token

    def error(self, message: str, token: Token | None = None) -> ParseError:
        offset = len(self.text) if token is None else token.offset
        return ParseError(f"構文エラー（位置 {offset + 1}）: {message}")

    def parse_sequent(self) -> Sequent:
        antecedent = self.parse_side("|-")
        self.expect("|-")
        succedent = self.parse_side(None)
        if self.peek() is not None:
            token = self.peek()
            raise self.error(f"余分なトークン {token.value!r} があります", token)
        return Sequent(antecedent, succedent)

    def parse_side(self, terminator: str | None) -> tuple[Prop, ...]:
        token = self.peek()
        if token is None or (terminator is not None and token.value == terminator):
            return ()

        props = [self.parse_imp()]
        while self.accept(","):
            token = self.peek()
            if token is None or (
                terminator is not None and token.value == terminator
            ):
                raise self.error("',' の後に命題が必要です", token)
            props.append(self.parse_imp())
        return tuple(props)

    def parse_prop(self) -> Prop:
        prop = self.parse_imp()
        token = self.peek()
        if token is not None:
            raise self.error(f"余分なトークン {token.value!r} があります", token)
        return prop

    def parse_imp(self) -> Prop:
        left = self.parse_or()
        if self.accept("->"):
            return Prop.binary("imp", left, self.parse_imp())
        return left

    def parse_or(self) -> Prop:
        node = self.parse_and()
        while self.accept("+"):
            node = Prop.binary("or", node, self.parse_and())
        return node

    def parse_and(self) -> Prop:
        node = self.parse_not()
        while self.accept("*"):
            node = Prop.binary("and", node, self.parse_not())
        return node

    def parse_not(self) -> Prop:
        if self.accept("~"):
            return Prop.unary("not", self.parse_not())
        return self.parse_primary()

    def parse_primary(self) -> Prop:
        if self.accept("("):
            node = self.parse_imp()
            self.expect(")")
            return node

        token = self.peek()
        if token is None:
            raise self.error("命題が必要ですが、入力が終わりました")
        if IDENTIFIER_RE.fullmatch(token.value) is None:
            raise self.error(f"命題が必要ですが、{token.value!r} が見つかりました", token)
        if token.value in RESERVED_IDENTIFIERS:
            raise self.error(
                f"{token.value!r} は .n3 の予約語なので命題変数にできません",
                token,
            )
        self.position += 1
        return Prop.variable(token.value)


def parse_prop(text: str) -> Prop:
    return Parser(text).parse_prop()


def parse_sequent(text: str) -> Sequent:
    return Parser(text).parse_sequent()


def _prop_precedence(prop: Prop) -> int:
    return {"imp": 1, "or": 2, "and": 3, "not": 4, "var": 5}[prop.kind]


def format_prop(prop: Prop) -> str:
    """README の優先順位を使い、必要な括弧だけを出力する。"""

    if prop.kind == "var":
        return prop.name
    if prop.kind == "not":
        operand = prop.args[0]
        rendered = format_prop(operand)
        if operand.kind not in {"var", "not"}:
            rendered = f"({rendered})"
        return f"~{rendered}"

    left, right = prop.args
    operator = {"and": "*", "or": "+", "imp": "->"}[prop.kind]
    precedence = _prop_precedence(prop)
    left_text = format_prop(left)
    right_text = format_prop(right)

    if _prop_precedence(left) < precedence or (
        prop.kind == "imp" and left.kind == "imp"
    ):
        left_text = f"({left_text})"

    if _prop_precedence(right) < precedence or (
        prop.kind in {"and", "or"} and right.kind == prop.kind
    ):
        right_text = f"({right_text})"

    return f"{left_text}{operator}{right_text}"


def _prop_key(prop: Prop) -> str:
    return format_prop(prop)


def format_sequent(sequent: Sequent) -> str:
    left = ", ".join(map(format_prop, sorted(sequent.ant, key=_prop_key)))
    right = ", ".join(map(format_prop, sorted(sequent.suc, key=_prop_key)))
    if left and right:
        return f"{left} |- {right}"
    if left:
        return f"{left} |-"
    if right:
        return f"|- {right}"
    return "|-"


def _logical_expansions(
    sequent: Sequent,
) -> Iterator[tuple[str, tuple[Prop, ...], tuple[Sequent, ...]]]:
    """通常の LK 規則を逆向きに適用した候補を列挙する。"""

    for principal in sorted(sequent.ant, key=_prop_key):
        if principal.kind == "var":
            continue
        rest = sequent.ant - {principal}
        if principal.kind == "and":
            left, right = principal.args
            yield (
                "andL",
                (left, right),
                (Sequent(rest | {left, right}, sequent.suc),),
            )
        elif principal.kind == "or":
            left, right = principal.args
            yield (
                "orL",
                (left, right),
                (
                    Sequent(rest | {left}, sequent.suc),
                    Sequent(rest | {right}, sequent.suc),
                ),
            )
        elif principal.kind == "imp":
            left, right = principal.args
            yield (
                "impL",
                (left, right),
                (
                    Sequent(rest, sequent.suc | {left}),
                    Sequent(rest | {right}, sequent.suc),
                ),
            )
        elif principal.kind == "not":
            operand = principal.args[0]
            yield (
                "notL",
                (operand,),
                (Sequent(rest, sequent.suc | {operand}),),
            )

    for principal in sorted(sequent.suc, key=_prop_key):
        if principal.kind == "var":
            continue
        rest = sequent.suc - {principal}
        if principal.kind == "and":
            left, right = principal.args
            yield (
                "andR",
                (left, right),
                (
                    Sequent(sequent.ant, rest | {left}),
                    Sequent(sequent.ant, rest | {right}),
                ),
            )
        elif principal.kind == "or":
            left, right = principal.args
            yield (
                "orR",
                (left, right),
                (Sequent(sequent.ant, rest | {left, right}),),
            )
        elif principal.kind == "imp":
            left, right = principal.args
            yield (
                "impR",
                (left, right),
                (Sequent(sequent.ant | {left}, rest | {right}),),
            )
        elif principal.kind == "not":
            operand = principal.args[0]
            yield (
                "notR",
                (operand,),
                (Sequent(sequent.ant | {operand}, rest),),
            )


@cache
def is_valid(sequent: Sequent) -> bool:
    """カットなし LK の可逆規則で古典命題論理の妥当性を判定する。"""

    if sequent.ant & sequent.suc:
        return True
    expansion = next(_logical_expansions(sequent), None)
    if expansion is None:
        return False
    return all(is_valid(premise) for premise in expansion[2])


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ProofConstructionError(message)


def apply_rule(
    rule: str,
    template_args: Sequence[Prop],
    premises: Sequence[Sequent],
) -> Sequent:
    """main.cpp と同じ集合操作で推論規則を前向きに評価する。"""

    templates = tuple(template_args)
    sequents = tuple(premises)

    if rule == "Id":
        _require(len(templates) == 1 and not sequents, "Id の引数が不正です")
        prop = templates[0]
        return Sequent({prop}, {prop})

    if rule in {"KL", "KR"}:
        _require(
            len(templates) == 1 and len(sequents) == 1,
            f"{rule} の引数が不正です",
        )
        prop, premise = templates[0], sequents[0]
        if rule == "KL":
            return Sequent(premise.ant | {prop}, premise.suc)
        return Sequent(premise.ant, premise.suc | {prop})

    if rule == "andL":
        left, right = templates
        (premise,) = sequents
        _require(left in premise.ant, "andL の左前提に第1成分がありません")
        _require(right in premise.ant, "andL の左前提に第2成分がありません")
        antecedent = (premise.ant - {left, right}) | {
            Prop.binary("and", left, right)
        }
        return Sequent(antecedent, premise.suc)

    if rule == "andR":
        left, right = templates
        first, second = sequents
        _require(first.ant == second.ant, "andR の左文脈が一致しません")
        _require(left in first.suc, "andR の第1前提に左成分がありません")
        _require(right in second.suc, "andR の第2前提に右成分がありません")
        first_rest = first.suc - {left}
        second_rest = second.suc - {right}
        _require(first_rest == second_rest, "andR の右文脈が一致しません")
        return Sequent(
            first.ant,
            first_rest | {Prop.binary("and", left, right)},
        )

    if rule == "orL":
        left, right = templates
        first, second = sequents
        _require(first.suc == second.suc, "orL の右文脈が一致しません")
        _require(left in first.ant, "orL の第1前提に左成分がありません")
        _require(right in second.ant, "orL の第2前提に右成分がありません")
        first_rest = first.ant - {left}
        second_rest = second.ant - {right}
        _require(first_rest == second_rest, "orL の左文脈が一致しません")
        return Sequent(
            first_rest | {Prop.binary("or", left, right)},
            first.suc,
        )

    if rule == "orR":
        left, right = templates
        (premise,) = sequents
        _require(left in premise.suc, "orR の右前提に第1成分がありません")
        _require(right in premise.suc, "orR の右前提に第2成分がありません")
        succedent = (premise.suc - {left, right}) | {
            Prop.binary("or", left, right)
        }
        return Sequent(premise.ant, succedent)

    if rule == "impL":
        left, right = templates
        first, second = sequents
        _require(left in first.suc, "impL の第1前提に前件がありません")
        _require(right in second.ant, "impL の第2前提に後件がありません")
        first_succedent = first.suc - {left}
        second_antecedent = second.ant - {right}
        _require(
            first.ant == second_antecedent
            and first_succedent == second.suc,
            "impL の文脈が一致しません",
        )
        return Sequent(
            second_antecedent | {Prop.binary("imp", left, right)},
            second.suc,
        )

    if rule == "impR":
        left, right = templates
        (premise,) = sequents
        _require(left in premise.ant, "impR の左前提に前件がありません")
        _require(right in premise.suc, "impR の右前提に後件がありません")
        return Sequent(
            premise.ant - {left},
            (premise.suc - {right}) | {Prop.binary("imp", left, right)},
        )

    if rule == "notL":
        (operand,) = templates
        (premise,) = sequents
        _require(operand in premise.suc, "notL の右前提に命題がありません")
        return Sequent(
            premise.ant | {Prop.unary("not", operand)},
            premise.suc - {operand},
        )

    if rule == "notR":
        (operand,) = templates
        (premise,) = sequents
        _require(operand in premise.ant, "notR の左前提に命題がありません")
        return Sequent(
            premise.ant - {operand},
            premise.suc | {Prop.unary("not", operand)},
        )

    raise ProofConstructionError(f"未知の推論規則です: {rule}")


def _make_proof(
    rule: str,
    template_args: tuple[Prop, ...],
    premises: tuple[Proof, ...],
) -> Proof:
    conclusion = apply_rule(
        rule,
        template_args,
        tuple(premise.conclusion for premise in premises),
    )
    return Proof(rule, template_args, premises, conclusion)


def synthesize(goal: Sequent) -> Proof:
    """C++ カーネルで目標と完全一致する証明木を生成する。"""

    if not is_valid(goal):
        raise UnprovableError(f"証明できないシークエントです: {goal}")

    @cache
    def build(sequent: Sequent) -> Proof:
        # 集合カーネルでは主式の成分と周辺文脈が衝突することがある。
        # 不要な文脈を弱化として先に分離すると、各論理規則を正確に適用できる。
        for prop in sorted(sequent.ant, key=_prop_key):
            smaller = Sequent(sequent.ant - {prop}, sequent.suc)
            if is_valid(smaller):
                proof = _make_proof("KL", (prop,), (build(smaller),))
                _require(proof.conclusion == sequent, "KL が目標を復元できません")
                return proof

        for prop in sorted(sequent.suc, key=_prop_key):
            smaller = Sequent(sequent.ant, sequent.suc - {prop})
            if is_valid(smaller):
                proof = _make_proof("KR", (prop,), (build(smaller),))
                _require(proof.conclusion == sequent, "KR が目標を復元できません")
                return proof

        common = sorted(sequent.ant & sequent.suc, key=_prop_key)
        if common:
            proof = _make_proof("Id", (common[0],), ())
            _require(proof.conclusion == sequent, "Id の結論が目標と一致しません")
            return proof

        for rule, template_args, premise_sequents in _logical_expansions(sequent):
            if not all(is_valid(premise) for premise in premise_sequents):
                continue
            try:
                reconstructed = apply_rule(rule, template_args, premise_sequents)
            except ProofConstructionError:
                continue
            if reconstructed != sequent:
                continue
            premises = tuple(build(premise) for premise in premise_sequents)
            proof = _make_proof(rule, template_args, premises)
            _require(
                proof.conclusion == sequent,
                f"{rule} が目標を復元できません",
            )
            return proof

        raise ProofConstructionError(
            f"妥当なシークエントの証明を構成できませんでした: {sequent}"
        )

    proof = build(goal)
    _require(proof.conclusion == goal, "生成した証明の結論が目標と一致しません")
    return proof


def _all_symbols(sequent: Sequent) -> set[str]:
    symbols: set[str] = set()

    def visit(prop: Prop) -> None:
        if prop.kind == "var":
            symbols.add(prop.name)
            return
        for arg in prop.args:
            visit(arg)

    for prop in sequent.ant | sequent.suc:
        visit(prop)
    return symbols


class ProofNameAllocator:
    def __init__(self, reserved: Iterable[str]):
        self.reserved = set(reserved) | set(RESERVED_IDENTIFIERS)
        self.next_index = 0

    def allocate(self) -> str:
        while True:
            candidate = f"proof{self.next_index}"
            self.next_index += 1
            if candidate not in self.reserved:
                self.reserved.add(candidate)
                return candidate


def emit_n3(goal: Sequent, root: Proof) -> str:
    """証明木を、README に記載された実行可能な .n3 へ変換する。"""

    symbols = sorted(_all_symbols(goal))
    lines = [f"Type {symbol};" for symbol in symbols]
    lines.append("")

    ordered: list[Proof] = []
    visited: set[int] = set()

    def visit(proof: Proof) -> None:
        identity = id(proof)
        if identity in visited:
            return
        for premise in proof.premises:
            visit(premise)
        visited.add(identity)
        ordered.append(proof)

    visit(root)

    allocator = ProofNameAllocator(symbols)
    names = {id(proof): allocator.allocate() for proof in ordered}

    for proof in ordered:
        template_text = ",".join(map(format_prop, proof.template_args))
        premise_text = ", ".join(names[id(premise)] for premise in proof.premises)
        expression = f"{proof.rule}<{template_text}>({premise_text})"
        name = names[id(proof)]
        if proof is root:
            lines.append(f"[{format_sequent(goal)}] {name} = {expression};")
        else:
            lines.append(f"auto {name} = {expression};")

    lines.append(f"print {names[id(root)]};")
    return "\n".join(lines) + "\n"


def generate_n3(text: str = DEFAULT_SEQUENT) -> str:
    goal = parse_sequent(text)
    return emit_n3(goal, synthesize(goal))


def prove(text: str = DEFAULT_SEQUENT) -> None:
    """従来どおり標準出力へ証明を生成するための小さな互換 API。"""

    sys.stdout.write(generate_n3(text))


def _argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="シークエントから README 準拠の .n3 証明を生成します。",
    )
    parser.add_argument(
        "sequent",
        nargs="?",
        default=DEFAULT_SEQUENT,
        help=f"証明するシークエント（省略時: {DEFAULT_SEQUENT!r}）",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        help="生成した .n3 を指定したファイルへ保存します。",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _argument_parser()
    args = parser.parse_args(argv)
    try:
        generated = generate_n3(args.sequent)
        if args.output is None:
            sys.stdout.write(generated)
        else:
            args.output.write_text(generated, encoding="utf-8")
    except ProofAssistantError as error:
        parser.exit(1, f"error: {error}\n")
    except ProofConstructionError as error:
        parser.exit(1, f"internal error: {error}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
