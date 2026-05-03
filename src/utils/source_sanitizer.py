from __future__ import annotations


def strip_solidity_comments(source: str) -> str:
    """
    Remove Solidity line/block comments while preserving strings and line breaks.

    The LLM stages should reason over executable code rather than commented-out
    guards such as `// onlyOwner`, which can otherwise be mistaken for live
    authorization logic.
    """
    if not source:
        return source

    result: list[str] = []
    i = 0
    in_line_comment = False
    in_block_comment = False
    in_single_quote = False
    in_double_quote = False

    while i < len(source):
        ch = source[i]
        nxt = source[i + 1] if i + 1 < len(source) else ""

        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                result.append(ch)
            else:
                result.append(" ")
            i += 1
            continue

        if in_block_comment:
            if ch == "*" and nxt == "/":
                result.extend("  ")
                in_block_comment = False
                i += 2
                continue
            result.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if in_single_quote:
            result.append(ch)
            if ch == "\\" and i + 1 < len(source):
                result.append(source[i + 1])
                i += 2
                continue
            if ch == "'":
                in_single_quote = False
            i += 1
            continue

        if in_double_quote:
            result.append(ch)
            if ch == "\\" and i + 1 < len(source):
                result.append(source[i + 1])
                i += 2
                continue
            if ch == '"':
                in_double_quote = False
            i += 1
            continue

        if ch == "/" and nxt == "/":
            result.extend("  ")
            in_line_comment = True
            i += 2
            continue

        if ch == "/" and nxt == "*":
            result.extend("  ")
            in_block_comment = True
            i += 2
            continue

        if ch == "'":
            in_single_quote = True
            result.append(ch)
            i += 1
            continue

        if ch == '"':
            in_double_quote = True
            result.append(ch)
            i += 1
            continue

        result.append(ch)
        i += 1

    return "\n".join(line.rstrip() for line in "".join(result).splitlines())
