import re
from pathlib import Path
from typing import Callable, Dict, Iterable, List


SOURCE_FILE = Path(__file__).with_name("cleaned.gbnf")
OUTPUT_FILE = Path(__file__).with_name("token_minimized.gbnf")

DEFINITION_PATTERN = re.compile(
    r"^([A-Za-z0-9_-]+)\s*::=([\s\S]*?)(?=^[A-Za-z0-9_-]+\s*::=|\Z)",
    re.MULTILINE,
)


def split_camel(name: str) -> List[str]:
    """Split a camelCase or mixed-case name into its component words."""
    return re.findall(r"[A-Z]?[a-z]+|[A-Z]+(?![a-z])|[0-9]+", name)


def build_camel_name(term: str, used: Iterable[str]) -> str:
    """Create a compact name for camelCase terms."""
    words = split_camel(term)
    if len(words) < 2:
        return build_lowercase_name(term, used)

    first = words[0][0].lower()
    second = words[1]
    candidate = first + second[0]
    idx = 1
    used_set = set(used)
    while candidate in used_set and idx < len(second):
        idx += 1
        candidate = first + second[:idx]

    if candidate in used_set:
        suffix = 2
        base = candidate
        while f"{base}{suffix}" in used_set:
            suffix += 1
        candidate = f"{base}{suffix}"

    return candidate


def build_lowercase_name(term: str, used: Iterable[str]) -> str:
    """Trim lowercase terms to the first four characters, extending as needed."""
    used_set = set(used)
    idx = 4
    candidate = term[:idx]

    while (candidate in used_set or candidate.endswith(("-", "_"))) and idx < len(term):
        idx += 1
        candidate = term[:idx]

    if candidate in used_set or candidate.endswith(("-", "_")):
        cleaned = term.replace("-", "").replace("_", "")
        if not cleaned:
            cleaned = term
        idx = 4
        candidate = cleaned[:idx] if idx <= len(cleaned) else cleaned
        while candidate in used_set and idx < len(cleaned):
            idx += 1
            candidate = cleaned[:idx]
        suffix = 2
        base = candidate
        while candidate in used_set:
            candidate = f"{base}{suffix}"
            suffix += 1

    return candidate


def build_rename_map(terms: List[str]) -> Dict[str, str]:
    """Build a mapping from the original term names to their compact forms."""
    rename: Dict[str, str] = {}
    used: List[str] = []

    for term in terms:
        if len(term) <= 4:
            rename[term] = term
            used.append(term)

    for term in terms:
        if len(term) <= 4:
            continue
        if any(c.isupper() for c in term):
            new_name = build_camel_name(term, used)
        else:
            new_name = build_lowercase_name(term, used)
        rename[term] = new_name
        used.append(new_name)

    if len(set(rename.values())) != len(rename.values()):
        raise ValueError("Failed to produce unique renamed terms.")

    return rename


def compile_replacer(rename_map: Dict[str, str]) -> Callable[[str], str]:
    """Return a function that substitutes term names according to the rename map."""
    ordered_terms = sorted(rename_map.keys(), key=len, reverse=True)
    pattern = re.compile(
        r"(?<![A-Za-z0-9_-])(" + "|".join(re.escape(t) for t in ordered_terms) + r")(?![A-Za-z0-9_-])"
    )
    string_pattern = re.compile(r'"(?:[^"\\]|\\.)*"')

    def _replace(text: str) -> str:
        parts: List[str] = []
        last = 0
        for match in string_pattern.finditer(text):
            segment = text[last : match.start()]
            parts.append(pattern.sub(lambda m: rename_map[m.group(0)], segment))
            parts.append(match.group(0))
            last = match.end()
        tail = text[last:]
        parts.append(pattern.sub(lambda m: rename_map[m.group(0)], tail))
        return "".join(parts)

    return _replace


def cleanup_pipe_spacing(text: str) -> str:
    """Remove unnecessary whitespace around pipe operators while keeping indentation."""
    def _clean_line(line: str) -> str:
        line = line.rstrip()
        line = re.sub(r"(?<=\S) \| (?=\S)", "|", line)
        line = re.sub(r"(?<=\S) \|", "|", line)
        line = re.sub(r"\| (?=\S)", "|", line)
        line = re.sub(r"\| +$", "|", line)
        return line

    return "\n".join(_clean_line(line) for line in text.split("\n"))


def format_module(rename_map: Dict[str, str]) -> str:
    """Format the module definition onto a single line inside the parentheses."""
    segments = [
        rename_map["line"],
        rename_map["sp"],
        '"MODULE"',
        rename_map["sp"],
        rename_map["name"],
        rename_map["sp"],
        rename_map["line"],
        rename_map["ws"],
        f"({rename_map['extends']} {rename_map['ws']})?",
        f"({rename_map['unit']} {rename_map['ws']})*",
        rename_map["dline"],
    ]
    return "(" + " ".join(segments) + ")"


def format_p10(rename_map: Dict[str, str]) -> str:
    """Format the p10 rule to keep the inner parenthetical expression on one line."""
    powerset = rename_map["powerset"]
    flatten = rename_map["flatten"]
    domain = rename_map["domain"]
    ws = rename_map["ws"]
    p14 = rename_map["p14-op"]
    p11 = rename_map["p11-op"]
    plus = rename_map["plus"]
    cross_prod = rename_map["crossProd"]
    mod = rename_map["mod"]
    p12 = rename_map["p12-op"]

    first_line = f"(({powerset}|{flatten}|{domain}) {ws})? {p14}|"
    inner = f"{ws} ({plus} {ws} {p11}|{cross_prod} {ws} {p14})"
    second_line = f"  {p11} ({inner})* ({ws} {mod} {ws} {p12})?"
    return f"{first_line}\n{second_line}"


def format_primary(rename_map: Dict[str, str]) -> str:
    """Collapse the primary alternatives onto a single line."""
    alternatives = [
        "name",
        "number",
        "string",
        "boolean",
        "knownSet",
        "group",
        "opCall",
        "quantify",
        "choose",
        "set",
        "actionSq",
        "conjlist",
        "disjlist",
        "recordSet",
        "record",
        "ternary",
    ]
    renamed = [rename_map[item] for item in alternatives]
    return "|".join(renamed)


def build_definition(
    term: str,
    rhs: str,
    rename_map: Dict[str, str],
    replacer: Callable[[str], str],
) -> str:
    """Produce the transformed definition without trailing newlines."""
    new_term = rename_map[term]

    if term == "module":
        rhs_text = format_module(rename_map)
        return f"{new_term} ::= {rhs_text}"
    if term == "p10-op":
        rhs_text = format_p10(rename_map)
        rhs_text = cleanup_pipe_spacing(rhs_text)
        return f"{new_term} ::= {rhs_text}"
    if term == "primary":
        rhs_text = format_primary(rename_map)
        return f"{new_term} ::= {rhs_text}"

    renamed_rhs = replacer(rhs)
    renamed_rhs = cleanup_pipe_spacing(renamed_rhs)

    if renamed_rhs.startswith("\n"):
        return f"{new_term} ::={renamed_rhs}"

    inline_rhs = renamed_rhs.lstrip()
    return f"{new_term} ::= {inline_rhs}"


def transform() -> None:
    text = SOURCE_FILE.read_text()
    matches = list(DEFINITION_PATTERN.finditer(text))
    terms = [match.group(1) for match in matches]
    rename_map = build_rename_map(terms)
    replacer = compile_replacer(rename_map)

    transformed_parts: List[str] = []
    cursor = 0

    for match in matches:
        start, end = match.span()
        term = match.group(1)
        rhs = match.group(2)
        transformed_parts.append(text[cursor:start])

        trailing_newlines = len(rhs) - len(rhs.rstrip("\n"))
        rhs_body = rhs[: len(rhs) - trailing_newlines] if trailing_newlines else rhs

        definition = build_definition(term, rhs_body, rename_map, replacer)
        transformed_parts.append(definition)
        transformed_parts.append("\n" * trailing_newlines)
        cursor = end

    transformed_parts.append(text[cursor:])

    OUTPUT_FILE.write_text("".join(transformed_parts))


if __name__ == "__main__":
    transform()
